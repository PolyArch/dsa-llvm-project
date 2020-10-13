//===-- RISCVInstrInfoSS.td - RISC-V 'SS' instructions -------*- tablegen -*-===//
//
// Stream Specialized Instruction Extension.
//
//===----------------------------------------------------------------------===//

//===----------------------------------------------------------------------===//
// Operand and SDNode transformation definitions.
//===----------------------------------------------------------------------===//

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CFG_PORT : RVInstS<0, OPC_CUSTOM_0,
                          (outs),
                          (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                          "ss_cfg_port", "$rs1, $rs2, $simm12">,
                          Sched<[SSRead, SSWrite]>;

let rd = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CFG : RVInstI<1, OPC_CUSTOM_0,
                     (outs),
                     (ins simm12:$simm12, GPR:$rs1),
                     "ss_cfg", "$rs1, $simm12">,
                     Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_FILL_MODE : RVInstS<3, OPC_CUSTOM_0,
                           (outs),
                           (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                           "ss_fill_mode", "$rs1, $rs2, $simm12">,
                           Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_ADD_PORT : RVInstS<0, OPC_CUSTOM_1,
                        (outs),
                        (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                        "ss_add_port", "$rs1, $rs2, $simm12">,
                        Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_DMA_RD : RVInstS<3, OPC_CUSTOM_1,
                        (outs),
                        (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                        "ss_dma_rd", "$rs1, $rs2, $simm12">,
                        Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CONST : RVInstS<4, OPC_CUSTOM_1,
                       (outs),
                       (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                       "ss_const", "$rs1, $rs2, $simm12">,
                       Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_RECV : RVInstS<5, OPC_CUSTOM_1,
                       (outs GPR:$rd),
                       (ins GPR:$rs1, simm12:$simm12),
                       "ss_recv", "$rd, $rs1, $simm12">,
                       Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_ATOM_OP : RVInstS<6, OPC_CUSTOM_1,
                       (outs),
                       (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                       "ss_atom_op", "$rs1, $rs2, $simm12">,
                       Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_WR_DMA : RVInstS<3, OPC_CUSTOM_2,
                        (outs),
                        (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                        "ss_wr_dma", "$rs1, $rs2, $simm12">,
                        Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_WR_RD : RVInstS<5, OPC_CUSTOM_2,
                       (outs),
                       (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                       "ss_wr_rd", "$rs1, $rs2, $simm12">,
                       Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CFG_ATOM_OP : RVInstS<7, OPC_CUSTOM_2,
                       (outs),
                       (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                       "ss_cfg_atom_op", "$rs1, $rs2, $simm12">,
                       Sched<[SSRead, SSWrite]>;

let rd = 0, hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_SET_ITER : RVInstI<2, OPC_CUSTOM_3,
                         (outs),
                         (ins GPR:$rs1),
                         "ss_set_iter", "$rs1">,
                         Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_WAIT : RVInstS<4, OPC_CUSTOM_3,
                      (outs),
                      (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                      "ss_wait", "$rs1, $rs2, $simm12">,
                      Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_IND : RVInstS<5, OPC_CUSTOM_3,
                      (outs),
                      (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                      "ss_ind", "$rs1, $rs2, $simm12">,
                      Sched<[SSRead, SSWrite]>;

let hasSideEffects = 1, mayLoad = 1, mayStore = 1 in
def SS_CFG_IND : RVInstS<7, OPC_CUSTOM_3,
                      (outs),
                      (ins GPR:$rs1, GPR:$rs2, simm12:$simm12),
                      "ss_cfg_ind", "$rs1, $rs2, $simm12">,
                      Sched<[SSRead, SSWrite]>;