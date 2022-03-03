(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2020      Henny Sipma
   Copyrigth (c) 2021-2022 Aarno Labs LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:
 
   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.
  
   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* chlib *)
open CHLanguage
open CHPretty

(* chutil *)
open CHPrettyUtil
open CHSumTypeSerializer

(* bchlib *)
open BCHBasicTypes
open BCHLibTypes

module H = Hashtbl
         
let calling_convention_mfts: calling_convention_t mfts_int =
  mk_mfts "calling_convention_t" [  (StdCall, "s"); (CDecl, "c") ]


let relational_op_mfts: relational_op_t mfts_int =
  mk_mfts
    "relational_op_t"
    [(PEquals, "eq");
     (PLessThan, "lt");
     (PLessEqual, "le");
     (PGreaterThan, "gt");
     (PGreaterEqual, "ge");
     (PNotEqual, "ne")]


let arithmetic_op_mfts: arithmetic_op_t mfts_int =
  mk_mfts
    "arithmetic_op_t"
    [(PPlus, "p"); (PMinus, "m"); (PDivide, "d"); (PTimes, "t")]


let g_arithmetic_op_mfts: g_arithmetic_op mfts_int =
  mk_mfts
    "g_arithmetic_op"
    [(GPlus, "p"); (GMinus, "m"); (GDivide, "d"); (GTimes, "t")]


let arg_io_mfts: arg_io_t mfts_int =
  mk_mfts  "arg_io_t" [ (ArgRead, "r"); (ArgReadWrite, "rw"); (ArgWrite, "w") ]


let formatstring_type_mfts: formatstring_type_t mfts_int  =
  mk_mfts
    "formatstring_type_t"
    [ (NoFormat, "n"); (PrintFormat, "p"); (ScanFormat, "s") ]


let eflag_mfts: eflag_t mfts_int =
  mk_mfts
    "eflag_t"
    [ (OFlag, "o"); (CFlag, "c"); (ZFlag, "z"); (SFlag, "s"); (PFlag, "p");
      (DFlag, "d"); (IFlag, "i") ]


let cpureg_mfts: cpureg_t mfts_int =
  mk_mfts
    "cpureg_t"
    [ (Eax,"eax"); (Ecx,"ecx"); (Ebp,"ebp"); (Ebx,"ebx"); (Edx,"edx"); (Esp,"esp");
      (Edi,"edi"); (Esi,"esi"); (Ax,"ax"); (Cx,"cx"); (Dx,"dx"); (Bx,"bx");
      (Sp,"sp"); (Bp,"bp"); (Si,"si"); (Di,"di"); (Al,"al"); (Cl,"cl");
      (Dl,"dl"); (Bl,"bl"); (Ah,"ah"); (Ch,"ch"); (Dh,"dh"); (Bh,"bh") ]


let mips_reg_mfts: mips_reg_t mfts_int =
  mk_mfts
    "mips_reg_t"
    [ (MRzero,"zero"); (MRat,"at"); (MRv0,"v0"); (MRv1,"v1"); (MRa0,"a0");
      (MRa1,"a1"); (MRa2,"a2"); (MRa3,"a3"); (MRt0,"t0"); (MRt1,"t1");
      (MRt2,"t2"); (MRt3,"t3"); (MRt4,"t4"); (MRt5,"t5"); (MRt6,"t6");
      (MRt7,"t7"); (MRs0,"s0"); (MRs1,"s1"); (MRs2,"s2"); (MRs3,"s3");
      (MRs4,"s4"); (MRs5,"s5"); (MRs6,"s6"); (MRs7,"s7"); (MRt8,"t8");
      (MRt9,"t9"); (MRk0,"k0"); (MRk1,"k1"); (MRgp,"gp"); (MRsp,"sp");
      (MRfp,"fp"); (MRra,"ra") ]


let arm_reg_mfts: arm_reg_t mfts_int =
  mk_mfts
    "arm_reg_t"
    [ (AR0, "R0");
      (AR1, "R1");
      (AR2, "R2");
      (AR3, "R3");
      (AR4, "R4");
      (AR5, "R5");
      (AR6, "R6");
      (AR7, "R7");
      (AR8, "R8");
      (AR9, "R9");
      (AR10, "R10");
      (AR11, "R11");
      (AR12, "R12");
      (ARSP, "SP");
      (ARLR, "LR");
      (ARPC, "PC") ]
                                                              
let mips_special_reg_mfts: mips_special_reg_t mfts_int =
  mk_mfts "mips_special_reg_t" [(MMHi,"hi");  (MMLo,"lo")]

let arm_special_reg_mfts: arm_special_reg_t mfts_int =
  mk_mfts
    "arm_special_reg_t"
    [(APSR, "APSR"); (FPSCR, "FPSCR"); (APSR_nzcv, "APSR_nzcv")]

let segment_mfts: segment_t mfts_int =
  mk_mfts
    "segment_t"
    [ (StackSegment,"ss"); (CodeSegment,"cs"); (DataSegment,"ds");
      (ExtraSegment,"es"); (FSegment,"fs"); (GSegment,"gs") ]

let arithmetic_op_mfts: arithmetic_op_t mfts_int =
  mk_mfts
    "arithmetic_op" [ (PPlus,"p"); (PMinus,"m"); (PDivide,"d"); (PTimes,"t") ]


let arm_extension_reg_type_mfts: arm_extension_reg_type_t mfts_int =
  mk_mfts
    "arm_extension_reg_type"
    [(XSingle, "S"); (XDouble, "D"); (XQuad, "Q")]


class register_mcts_t:[register_t] mfts_int =
object

  inherit [register_t] mcts_t "register_t"

  method ts (r:register_t) =
    match r with
    | SegmentRegister _ -> "s"
    | CPURegister _ -> "c"
    | DoubleRegister _ -> "d"
    | FloatingPointRegister _ -> "f"
    | ControlRegister _ -> "ctr"
    | DebugRegister _ -> "dbg"
    | MmxRegister _ -> "m"
    | XmmRegister _ -> "x"
    | MIPSRegister _ -> "p"
    | MIPSSpecialRegister _ -> "ps"
    | MIPSFloatingPointRegister _ -> "pfp"
    | ARMRegister _ -> "a"
    | ARMSpecialRegister _ -> "as"
    | ARMExtensionRegister _ -> "armx"
    | ARMExtensionRegisterElement _ -> "armxe"
    | ARMExtensionRegisterReplicatedElement _ -> "armxr"
    | PowerGPRegister _ -> "pwrgpr"

  method tags = [
      "a"; "armx"; "armxe"; "armxr"; "as"; "c"; "ctr"; "d"; "dbg"; "f";
      "m"; "s"; "x"; "p"; "pfp"; "ps"; "pwrgpr"]

end

let register_mcts: register_t mfts_int = new register_mcts_t


class parameter_location_mcts_t: [parameter_location_t] mfts_int =
object

  inherit [ parameter_location_t ] mcts_t "parameter_location"

  method ts (p:parameter_location_t) =
    match p with
    | StackParameter _ -> "s"
    | RegisterParameter _ -> "r"
    | GlobalParameter _ -> "g"
    | UnknownParameterLocation -> "u"

  method tags = [ "g"; "r"; "s"; "u" ]

end

let parameter_location_mcts: parameter_location_t mfts_int =
  new parameter_location_mcts_t


class bterm_mcts_t: [bterm_t] mfts_int =
object

  inherit [ bterm_t ] mcts_t "bterm"

  method ts (t:bterm_t) =
    match t with
    | ArgValue _ -> "a"
    | RunTimeValue -> "rt"
    | ReturnValue -> "r"
    | NamedConstant _ -> "n"
    | NumConstant _ -> "c"
    | ArgBufferSize _ -> "s"
    | IndexSize _ -> "i"
    | ByteSize _ -> "b"
    | ArgAddressedValue _ -> "aa"
    | ArgNullTerminatorPos _ -> "nt"
    | ArgSizeOf _ -> "as"
    | ArithmeticExpr _ -> "x"

  method tags = ["a"; "aa"; "as"; "b"; "c"; "i"; "n"; "nt"; "r"; "rt"; "s"; "x"]

end

let bterm_mcts: bterm_t mfts_int = new bterm_mcts_t


class gterm_mcts_t: [gterm_t] mfts_int =
object

  inherit [gterm_t] mcts_t "gterm"

  method ts (t: gterm_t) =
    match t with
    | GConstant _ -> "c"
    | GReturnValue _ -> "r"
    | GSideeffectValue _ -> "s"
    | GArgValue _ -> "a"
    | GUnknownValue -> "u"
    | GArithmeticExpr _ -> "x"

  method tags = ["a"; "c"; "r"; "s"; "u"; "x"]

end

let gterm_mcts: gterm_t mfts_int = new gterm_mcts_t


class function_stub_mcts_t: [function_stub_t] mfts_int =
object

  inherit [ function_stub_t ] mcts_t "function_stub"

  method ts (s:function_stub_t) =
    match s with
    | SOFunction _ -> "so"
    | DllFunction _ -> "dll"
    | JniFunction _ -> "jni"
    | LinuxSyscallFunction _ -> "sc"
    | PckFunction _ -> "pck"

  method tags = ["dll"; "jni"; "pck"; "so"; "sc"]

end

let function_stub_mcts: function_stub_t mfts_int = new function_stub_mcts_t


class call_target_mcts_t: [call_target_t] mfts_int =
object

  inherit [call_target_t] mcts_t "call_target"

  method ts (c:call_target_t) =
    match c with
    | StubTarget _ -> "stub"
    | StaticStubTarget _ -> "sstub"
    | AppTarget _ -> "app"
    | InlinedAppTarget _ -> "inl"
    | WrappedTarget _ -> "wrap"
    | VirtualTarget _ -> "v"
    | IndirectTarget _ -> "i"
    | CallbackTableTarget _ -> "cb"
    | UnknownTarget -> "u"

  method tags = ["app"; "cb"; "i"; "inl"; "stub"; "sstub"; "u"; "v"; "wrap"]

end

let call_target_mcts: call_target_t mfts_int = new call_target_mcts_t

class c_struct_constant_mcts_t: [c_struct_constant_t] mfts_int =
object

  inherit [c_struct_constant_t] mcts_t "c_struct_constant"

  method ts (c:c_struct_constant_t) =
    match c with
    | FieldValues _ -> "v"
    | FieldConstant _ -> "c"
    | FieldString _ -> "s"
    | FieldCallTarget _ -> "t"

  method tags = ["c"; "s"; "t"; "v"]

end

let c_struct_constant_mcts: c_struct_constant_t mfts_int =
  new c_struct_constant_mcts_t


class precondition_mcts_t: [precondition_t] mfts_int =
object

  inherit [precondition_t] mcts_t "precondition_t"

  method ts (p: precondition_t) =
    match p with
    | PreNullTerminated _ -> "nt"
    | PreNotNull _ -> "nn"
    | PreNull _ -> "nu"
    | PreDerefRead _ -> "dr"
    | PreDerefWrite _ -> "dw"
    | PreAllocationBase _ -> "ab"
    | PreFunctionPointer _ -> "fp"
    | PreNoOverlap _ -> "nov"
    | PreFormatString _ -> "fs"
    | PreEnum _ -> "en"
    | PreRelationalExpr _ -> "re"
    | PreDisjunction _ -> "dj"
    | PreConditional _ -> "c"
    | PreIncludes _ -> "ic"

  method tags = [
      "ab"; "c"; "dj"; "dr"; "dw"; "en"; "fp"; "fs"; "ic";
      "nn"; "nov"; "nt"; "nu"; "re"]

end

let precondition_mcts: precondition_t mfts_int =
  new precondition_mcts_t


class postcondition_mcts_t: [postcondition_t] mfts_int =
object

  inherit [postcondition_t] mcts_t "postcondition_t"

  method ts (p: postcondition_t) =
    match p with
    | PostNewMemoryRegion _ -> "nm"
    | PostFunctionPointer _ -> "fp"
    | PostAllocationBase _ -> "ab"
    | PostNotNull _ -> "nn"
    | PostNull _ -> "nu"
    | PostNullTerminated _ -> "nt"
    | PostEnum _ -> "en"
    | PostFalse -> "f"
    | PostRelationalExpr _ -> "re"
    | PostDisjunction _ -> "dj"
    | PostConditional _ -> "c"

  method tags = [
      "ab"; "c"; "dj"; "en"; "f"; "fp"; "nm"; "nn"; "nt"; "nu"; "re"]

end

let postcondition_mcts: postcondition_t mfts_int =
  new postcondition_mcts_t


class sideeffect_mcts_t: [sideeffect_t] mfts_int =
object

  inherit [sideeffect_t] mcts_t "sideeffect_t"

  method ts (s: sideeffect_t) =
    match s with
    | BlockWrite _ -> "bw"
    | Modifies _ -> "m"
    | AllocatesStackMemory _ -> "as"
    | StartsThread _ -> "st"
    | Invalidates _ -> "i"
    | SetsErrno -> "se"
    | ConditionalSideeffect _ -> "c"
    | UnknownSideeffect -> "u"

  method tags = ["as"; "bw"; "c"; "i"; "m"; "se"; "st"; "u"]

end


let sideeffect_mcts: sideeffect_t mfts_int =
  new sideeffect_mcts_t


class memory_base_mcts_t:[ memory_base_t ] mfts_int =
object

  inherit [ memory_base_t ] mcts_t "memory_base"

  method ts (b:memory_base_t) =
    match b with
    | BLocalStackFrame -> "l"
    | BRealignedStackFrame -> "r"
    | BAllocatedStackFrame -> "a"
    | BGlobal -> "g"
    | BaseVar _ -> "v"
    | BaseUnknown _ -> "u"

  method tags = [ "a"; "g"; "l"; "r"; "u"; "v" ]
end

let memory_base_mcts: memory_base_t mfts_int = new memory_base_mcts_t

class memory_offset_mcts_t: [ memory_offset_t ] mfts_int =
object

  inherit [ memory_offset_t ] mcts_t "memory_offset"

  method ts (o:memory_offset_t) =
    match o with
    | NoOffset -> "n"
    | ConstantOffset _ -> "c"
    | IndexOffset _ -> "i"
    | UnknownOffset -> "u"

  method tags = [ "c"; "i"; "n"; "u" ]
end

let memory_offset_mcts: memory_offset_t mfts_int = new memory_offset_mcts_t

class assembly_variable_denotation_mcts_t:[assembly_variable_denotation_t] mfts_int =
object

  inherit [assembly_variable_denotation_t] mcts_t "assembly_variable"

  method ts (v:assembly_variable_denotation_t) =
    match v with
    | MemoryVariable _ -> "m"
    | RegisterVariable _ -> "r"
    | CPUFlagVariable _ -> "f"
    | AuxiliaryVariable _ -> "a"

  method tags = ["a"; "f"; "m"; "r"]

end

let assembly_variable_denotation_mcts: assembly_variable_denotation_t mfts_int =
  new assembly_variable_denotation_mcts_t

class constant_value_variable_mcts_t: [constant_value_variable_t] mfts_int =
object

  inherit [constant_value_variable_t] mcts_t "constant_value_variable"

  method ts (v:constant_value_variable_t) =
    match v with
    | InitialRegisterValue _ -> "ir"
    | InitialMemoryValue _ -> "iv"
    | FrozenTestValue _ -> "ft"
    | FunctionReturnValue _ -> "fr"
    | SyscallErrorReturnValue _ -> "ev"
    | FunctionPointer _ -> "fp"
    | CallTargetValue _ -> "ct"
    | SideEffectValue _ -> "se"
    | MemoryAddress  _ -> "ma"
    | BridgeVariable _ -> "bv"
    | FieldValue _ -> "fv"
    | SymbolicValue _ -> "sv"
    | SignedSymbolicValue _ -> "ssv"
    | Special _ -> "sp"
    | RuntimeConstant _ -> "rt"
    | ChifTemp -> "chiftemp"

  method tags = [
      "bv"; "chiftemp"; "ct"; "ev"; "fr"; "fp"; "ft"; "fv"; "ir";
      "iv"; "ma"; "rt"; "se" ; "sp"; "sv"]

end

let constant_value_variable_mcts:constant_value_variable_t mfts_int =
  new constant_value_variable_mcts_t


class jump_target_mcts_t: [ jump_target_t ] mfts_int =
object

  inherit [ jump_target_t ] mcts_t "jump_target"

  method ts (t:jump_target_t) =
    match t with
    | JumptableTarget _ -> "jt"
    | OffsettableTarget _ -> "ot"
    | JumpOnTerm _ -> "jb"
    | DllJumpTarget _ -> "dj"
    | SOJumpTarget _ -> "sj"
    | UnknownJumpTarget -> "u"

  method tags = [ "jt" ; "ot" ; "ja" ; "dj" ; "sj" ; "u" ]

end

let jump_target_mcts:jump_target_t mfts_int = new jump_target_mcts_t


class non_relational_value_mcts_t:[non_relational_value_t] mfts_int =
object

  inherit [non_relational_value_t] mcts_t "non_relational_value_t"

  method ts (v:non_relational_value_t) =
    match v with
    | FSymbolicExpr _ -> "sx"
    | FIntervalValue _ -> "iv"
    | FBaseOffsetValue _ -> "bv"

  method tags = [ "bv"; "iv"; "sx" ]
end

let non_relational_value_mcts:non_relational_value_t mfts_int =
  new non_relational_value_mcts_t

class invariant_fact_mcts_t: [invariant_fact_t] mfts_int =
object

  inherit [invariant_fact_t] mcts_t "invariant_fact_t"

  method ts (t:invariant_fact_t) =
    match t with
    | Unreachable _ -> "u"
    | NonRelationalFact _ -> "n"
    | RelationalFact _ -> "r"
    | InitialVarEquality _ -> "ie"
    | InitialVarDisEquality _ -> "id"
    | TestVarEquality _ -> "te"

  method tags = [ "id"; "ie"; "n"; "r"; "te" ; "u" ]

end

let invariant_fact_mcts:invariant_fact_t mfts_int =  new invariant_fact_mcts_t

class type_invariant_fact_mcts_t:[type_invariant_fact_t] mfts_int =
object

  inherit [type_invariant_fact_t] mcts_t "type_invariant_fact_t"

  method ts (t:type_invariant_fact_t) =
    match t with
    | VarTypeFact _ -> "v"
    | ConstTypeFact _ -> "c"
    | XprTypeFact _ -> "x"

  method tags = [ "v"; "c"; "x" ]

end

let type_invariant_fact_mcts:type_invariant_fact_t mfts_int =
  new type_invariant_fact_mcts_t
