//===-- RISCVInstrInfoSSP.td - RISC-V 'SSP' instructions ---*- tablegen -*-===// //
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file describes the RISC-V instructions for SSP extension.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Instruction class templates
//===----------------------------------------------------------------------===//

class RVInstSSP<bits<3> funct3, RISCVOpcode opcode, dag outs, dag ins,
              string opcodestr, string argstr>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatI> {
  let Inst{31-20} = 0;
  let Inst{19-15} = 0;
  let Inst{14-12} = funct3;
  let Inst{11-7} = 0;
  let Opcode = opcode.Value;
}

//===----------------------------------------------------------------------===//
// Instructions
//===----------------------------------------------------------------------===//


let rs1 = 0, rd = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_CONFIG: RVInstI<0b000, OPC_CUSTOM_0, 
                                (outs),
                                (ins simm12:$imm12),
                                "ssp.stream.config", "$imm12">;
let rs1 = 0, rd = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_END: RVInstI<0b001, OPC_CUSTOM_0, 
                            (outs),
                            (ins simm12:$imm12),
                            "ssp.stream.end", "$imm12">;
let rd = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_INPUT: RVInstI<0b010, OPC_CUSTOM_0, 
                              (outs),
                              (ins simm12:$imm12, GPR:$rs1),
                              "ssp.stream.input", "$imm12, $rs1">;
let rd = 0, rs1 = 0, imm12 = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_READY: RVInstI<0b011, OPC_CUSTOM_0, 
                              (outs),
                              (ins),
                              "ssp.stream.ready", "">;
let rs1 = 0, rd = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_STEP : RVInstI<0b100, OPC_CUSTOM_0, 
                              (outs),
                              (ins simm12:$imm12),
                              "ssp.stream.step", "$imm12">;
let rs1 = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_LOAD : RVInstI<0b000, OPC_CUSTOM_1, 
                              (outs GPR:$rd),
                              (ins simm12:$imm12),
                              "ssp.stream.ld", "$rd, $imm12">;

let Predicates = [HasStdExtD] in {

let rs1 = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_FLD : RVInstI<0b110, OPC_CUSTOM_1, 
                             (outs FPR64:$rd),
                             (ins simm12:$imm12),
                             "ssp.stream.fld", "$rd, $imm12">;

let rs1 = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SSP_STREAM_FLW : RVInstI<0b111, OPC_CUSTOM_1, 
                             (outs FPR32:$rd),
                             (ins simm12:$imm12),
                             "ssp.stream.flw", "$rd, $imm12">;

}

// let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
// def SSP_STREAM_CONFIG : RVInstSSP<0b000, OPC_CUSTOM_0, 
//                                   (outs),
//                                   (ins),
//                                   "ssp.stream.config", "">;

//===----------------------------------------------------------------------===//
// Pseudo-instructions and codegen patterns
//===----------------------------------------------------------------------===//

def SSPStreamConfigPat
    : Pat<(int_ssp_stream_config simm12:$config), (SSP_STREAM_CONFIG simm12:$config)>;
def SSPStreamEndPat 
    : Pat<(int_ssp_stream_end simm12:$config), (SSP_STREAM_END simm12:$config)>;
def SSPStreamInputPat
    : Pat<(int_ssp_stream_input simm12:$stream, GPR:$value), 
          (SSP_STREAM_INPUT simm12:$stream, GPR:$value)>;
def SSPStreamReadyPat
    : Pat<(int_ssp_stream_ready), 
          (SSP_STREAM_READY)>;
def SSPStreamStepPat 
    : Pat<(int_ssp_stream_step simm12:$stream), 
          (SSP_STREAM_STEP simm12:$stream)>;
def SSPStreamLoadPat 
    : Pat<(int_ssp_stream_load simm12:$stream), 
          (SSP_STREAM_LOAD simm12:$stream)>;
let Predicates = [HasStdExtD] in {
def SSPStreamFLDPat 
    : Pat<(int_ssp_stream_load simm12:$stream), 
          (SSP_STREAM_FLD simm12:$stream)>;
def SSPStreamFLWPat 
    : Pat<(int_ssp_stream_load simm12:$stream), 
          (SSP_STREAM_FLW simm12:$stream)>;
}