/**
 * SSP instructions' opcode are 0x0F 0x38 0x3X, with no prefix.
 */

class ISSP<bits<8> o, Format f, ImmType i, dag outs, dag ins, 
           string asm, list<dag> pattern>
  : X86Inst<o, f, i, outs, ins, asm>, T8 {
  let Pattern = pattern;
  let CodeSize = 3; 
}

def SSP_STREAM_CONFIG
  : ISSP<0x30, 
         RawFrm, 
         Imm8,
         (outs),
         (ins i64i8imm:$config),
         "ssp.stream.config\t{$config|$config}",
         [(int_ssp_stream_config i64immSExt8:$config)]>;

def SSP_STREAM_END
  : ISSP<0x31,
         RawFrm,
         Imm8,
         (outs),
         (ins i64i8imm:$config),
         "ssp.stream.end\t{$config|$config}",
         [(int_ssp_stream_end i64immSExt8:$config)]>;

/**
 * Notice that operands are reordered so register value comes first.
 * Use MRMXr to encode source register in R/M and not use R/O. 
 */
def SSP_STREAM_INPUT
  : ISSP<0x32,
         MRMXr,
         Imm8,
         (outs),
         (ins GR64:$value, i64i8imm:$stream),
         "ssp.stream.input\t{$stream, $value|$stream, $value}",
         [(int_ssp_stream_input i64immSExt8:$stream, GR64:$value)]>;

def SSP_STREAM_READY
  : ISSP<0x33,
         RawFrm,
         NoImm,
         (outs),
         (ins),
         "ssp.stream.ready",
         [(int_ssp_stream_ready)]>;

def SSP_STREAM_STEP
  : ISSP<0x34,
         RawFrm,
         Imm8,
         (outs),
         (ins i64i8imm:$stream),
         "ssp.stream.step\t{$stream|$stream}",
         [(int_ssp_stream_step i64immSExt8:$stream)]>;

def SSP_STREAM_LOAD64
  : ISSP<0x35,
         MRMXr,
         Imm8,
         (outs GR64:$dst),
         (ins i64i8imm:$stream),
         "ssp.stream.ld\t{$stream, $dst|$dst, $stream}",
         [(set GR64:$dst, (int_ssp_stream_load i64immSExt8:$stream))]>;
         