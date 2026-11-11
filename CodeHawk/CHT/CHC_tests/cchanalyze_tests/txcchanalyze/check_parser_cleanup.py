"""The parser must reject cleanup before unused-local removal can hide it."""
import pathlib
import subprocess
import sys
import tempfile

parser = pathlib.Path(sys.argv[1]).resolve()
fixture = pathlib.Path(sys.argv[2]).read_text()
declaration = 'unsigned guard __attribute__((cleanup(change_kind)));'
assert declaration in fixture
with tempfile.TemporaryDirectory(prefix='cleanup-parser-', dir='.') as directory:
    root = pathlib.Path(directory).resolve()
    for name, text in [
        ('unused', fixture),
        ('used', fixture.replace(declaration, declaration[:-1] + ' = input; input += guard;')),
        ('underscore', fixture.replace('cleanup(change_kind)', '__cleanup__(change_kind)')),
        ('plain', fixture.replace(declaration, 'unsigned guard;')),
    ]:
        source = root / (name + '.i')
        source.write_text(text)
        output = root / (name + '-output')
        output.mkdir()
        result = subprocess.run([str(parser), '-projectpath', str(root),
            '-targetdirectory', str(output), str(source)], text=True, capture_output=True)
        message = result.stdout + result.stderr
        if name == 'plain':
            assert result.returncode == 0, message
            assert any('codehawk_no_implicit_local_effects_v1' in p.read_text()
                       for p in output.rglob('*_cdict.xml'))
        else:
            assert result.returncode == 1, (name, message)
            assert 'Unsupported implicit cleanup effect' in message and 'guard' in message
            assert not list(output.rglob('*_cfun.xml')), 'Rejected input emitted function proofs'
print('parser cleanup: unused/used/underscore rejected; ordinary input certified')
