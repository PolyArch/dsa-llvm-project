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

class SSPSTREAMLOAD<bits<8> o, RegisterClass rc, ValueType vt, string suffix>
  : ISSP<o,
         MRMXr,
         Imm8,
         (outs rc:$dst),
         (ins i64i8imm:$stream),
         !strconcat("ssp.stream.ld.", suffix, "\t{$stream, $dst|$dst, $stream}"),
         [(set rc:$dst, (vt (int_ssp_stream_load i64immSExt8:$stream)))]>;

class VSSPSTREAMLOAD<bits<8> o, RegisterClass rc, ValueType vt, string suffix>
  : ISSP<o,
         MRM0r,
         Imm8,
         (outs rc:$dst),
         (ins i64i8imm:$stream),
         !strconcat("ssp.stream.ld.", suffix, "\t{$stream, $dst|$dst, $stream}"),
         [(set rc:$dst, (vt (int_ssp_stream_load i64immSExt8:$stream)))]>,
    EVEX, EVEX_V512 {
  Prefix OpPrefix = PS;
}

def SSP_STREAM_LOAD_I64    : SSPSTREAMLOAD<0x35, GR64, i64, "i64">;
def SSP_STREAM_LOAD_F32    : SSPSTREAMLOAD<0x36, FR32, f32, "f32">;
def SSP_STREAM_LOAD_F64    : SSPSTREAMLOAD<0x37, FR64, f64, "f64">;
def SSP_STREAM_LOAD_V4F32  : SSPSTREAMLOAD<0x38, VR128, v4f32, "v4f32">;
def SSP_STREAM_LOAD_V2F64  : SSPSTREAMLOAD<0x39, VR128, v2f64, "v2f64">;
def SSP_STREAM_LOAD_V4I32  : SSPSTREAMLOAD<0x3A, VR128, v4i32, "v4i32">;
def SSP_STREAM_LOAD_V2I64  : SSPSTREAMLOAD<0x3B, VR128, v2i64, "v2i64">;
def SSP_STREAM_LOAD_V4F64  : SSPSTREAMLOAD<0x3C, VR256, v4f64, "v4f64">;
def SSP_STREAM_LOAD_V8I64  : VSSPSTREAMLOAD<0x40, VR512, v8i64, "v8i64">;
def SSP_STREAM_LOAD_V16I32 : VSSPSTREAMLOAD<0x41, VR512, v16i32, "v16i32">;
def SSP_STREAM_LOAD_V8F64  : VSSPSTREAMLOAD<0x42, VR512, v8f64, "v8f64">;
def SSP_STREAM_LOAD_V16F32 : VSSPSTREAMLOAD<0x43, VR512, v16f32, "v16f32">;

def SSP_STREAM_LOAD_V8I16  : SSPSTREAMLOAD<0x45, VR128, v8i16, "v8i16">;

class VSSPSTREAMINPUT<bits<8> o, RegisterClass rc, ValueType vt, string suffix>
  : ISSP<o,
         MRM0r,
         Imm8,
         (outs),
         (ins rc:$value, i64i8imm:$stream),
         !strconcat("ssp.stream.input.", suffix, "\t{$stream, $value|$value, $stream}"),
         [(int_ssp_stream_input i64immSExt8:$stream, (vt rc:$value))]>,
    EVEX, EVEX_V512 {
  Prefix OpPrefix = PS;
}

def SSP_STREAM_INPUT_V16F32 : VSSPSTREAMINPUT<0x44, VR512, v16f32, "v16f32">;