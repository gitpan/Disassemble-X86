package Disassemble::X86;

use 5.006;
use strict;
use warnings;
use integer;
use Disassemble::X86::MemRegion;

our $VERSION = 0.01;

my $max_instr_len = 15;

my @longregs = qw(  eax  ecx  edx  ebx  esp  ebp  esi  edi );
my @wordregs = qw(   ax   cx   dx   bx   sp   bp   si   di );
my @byteregs = qw(   al   cl   dl   bl   ah   ch   dh   bh );
my @mmxregs  = qw(  mm0  mm1  mm2  mm3  mm4  mm5  mm6  mm7 );
my @xmmregs  = qw( xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 );
my %regs = (
  dword  => \@longregs,
  word   => \@wordregs,
  byte   => \@byteregs,
  qword  => \@mmxregs,
  dqword => \@xmmregs,
);

my @segregs = qw( es cs ss ds fs gs );
my @index16 = qw( bx+si bx+di bp+si bp+di si di bp bx );
my @immed_grp = qw( add or adc sbb and sub xor cmp );
my @shift_grp = qw( rol ror rcl rcr shl shr xxx sar );
my @unary_grp = qw( test test not neg mul imul div idiv );
my @bittst_grp = qw( bt bts btr btc );
my @float_op = qw( add mul com comp sub subr div divr );
my @prefetch_op = qw( nta t0 t1 t2 );
my @cond_code = qw( o no b ae e ne be a s ns pe po l ge le g );

my $mmx_proc    = 995;
my $tdnow_proc  = 996;
my $tdnow2_proc = 997;
my $sse_proc    = 998;
my $sse2_proc   = 999;
my %proc_xlat = (
    $mmx_proc    => "mmx",
    $tdnow_proc  => "3dnow",
    $tdnow2_proc => "3dnow-e",
    $sse_proc    => "sse",
    $sse2_proc   => "sse2",
);

sub new {
  my ($class, %args) = @_;
  my $self = bless { } => $class;

  my $text = $args{text};
  unless (ref $text) {
    $text = Disassemble::X86::MemRegion->new(
        mem => $text,
        start => $args{start} || 0,
    );
  }
  $self->{text} = $text;

  $self->pos( exists($args{pos}) ? $args{pos} : $text->start() );
  $self->{addr_size} = $self->{data_size} = "dword";
  $self->set_def_proc();
  $self->addr_size($args{addr_size} || $args{size} || "dword");
  $self->data_size($args{data_size} || $args{size} || "dword");
  $self->{seg_reg} = "";
  $self->{mmx_pre} = 0;
  return $self;
} # new

sub addr_size {
  my ($self, $size) = @_;
  if ($size) {
    if ($size eq "16" || $size eq "word") { $self->{addr_size} = "word" }
    elsif ($size eq "32" || $size eq "dword" || $size eq "long") {
      $self->{addr_size} = "dword";
    }
    else { return }
    $self->set_def_proc();
  }
  return $self->{addr_size};
} # addr_size

sub data_size {
  my ($self, $size) = @_;
  if ($size) {
    if ($size eq "16" || $size eq "word") { $self->{data_size} = "word" }
    elsif ($size eq "32" || $size eq "dword" || $size eq "long") {
      $self->{data_size} = "dword";
    }
    else { return }
    $self->set_def_proc();
  }
  return $self->{data_size};
} # data_size

sub set_def_proc {
  my ($self) = @_;
  $self->{def_proc} = ($self->{addr_size} eq "word"
      && $self->{data_size} eq "word") ? 86 : 386;
} # set_def_proc

sub text     { $_[0]->{text} }
sub at_end   { $_[0]->{pos} >= $_[0]->{text}->end() }
sub contains { $_[0]->{text}->contains($_[1]) }
sub op       { $_[0]->{op} }
sub op_start { $_[0]->{op_start} }
sub op_len   { $_[0]->{pos} - $_[0]->{op_start} }
sub op_error { $_[0]->{error} }

sub op_proc  {
  my $proc = $_[0]->{proc};
  return $proc_xlat{$proc} || $proc;
} # op_proc

sub pos {
  my ($self, $pos) = @_;
  if (defined $pos) {
    $self->{pos} = $pos;
    $self->{lim} = $pos + $max_instr_len;
  }
  return $self->{pos};
} # pos

sub disasm {
  my ($self) = @_;
  my $start = $self->{op_start} = $self->{pos};
  $self->{lim} = $start + $max_instr_len;
  my $def_proc = $self->{proc} = $self->{def_proc};
  $self->{error} = "";
  my $op = $self->_disasm();
  $self->{proc} = $def_proc if $self->{proc} < $def_proc;
  $self->{pos} > $self->{lim} and $self->{error} = "opcode too long";
  $self->{error} and undef $op;
  unless (defined $op) { $self->{pos} = $start; $self->{proc} = 0; }
  return $self->{op} = $op;
} # disasm

sub _disasm {
  my ($self) = @_;
  my $byte = $self->next_byte();
  if ($byte >= 0x00 && $byte <= 0x05) {
    return $self->arith_op("add", $byte);
  }
  elsif ($byte == 0x06) { return "push es" }
  elsif ($byte == 0x07) { return "pop es" }
  elsif ($byte >= 0x08 && $byte <= 0x0d) {
    return $self->arith_op("or", $byte);
  }
  elsif ($byte == 0x0e) { return "push cs" }
  elsif ($byte == 0x0f) { return $self->twobyte() }
  elsif ($byte >= 0x10 && $byte <= 0x15) {
    return $self->arith_op("adc", $byte);
  }
  elsif ($byte == 0x16) { return "push ss" }
  elsif ($byte == 0x17) { return "pop ss" }
  elsif ($byte >= 0x18 && $byte <= 0x1d) {
    return $self->arith_op("sbb", $byte);
  }
  elsif ($byte == 0x1e) { return "push ds" }
  elsif ($byte == 0x1f) { return "pop ds" }
  elsif ($byte >= 0x20 && $byte <= 0x25) {
    return $self->arith_op("and", $byte);
  }
  elsif ($byte == 0x26) { return $self->seg_op("es") }
  elsif ($byte == 0x27) { return "daa" }
  elsif ($byte >= 0x28 && $byte <= 0x2d) {
    return $self->arith_op("sub", $byte);
  }
  elsif ($byte == 0x2e) {
    my $op = $self->seg_op("cs");
    return "$op,hint_no" if defined($op) && $op =~ /^j[^m]/;
    return $op;
  }
  elsif ($byte == 0x2f) { return "das" }
  elsif ($byte >= 0x30 && $byte <= 0x35) {
    return $self->arith_op("xor", $byte);
  }
  elsif ($byte == 0x36) { return $self->seg_op("ss") }
  elsif ($byte == 0x37) { return "aaa" }
  elsif ($byte >= 0x38 && $byte <= 0x3d) {
    return $self->arith_op("cmp", $byte);
  }
  elsif ($byte == 0x3e) {
    my $op = $self->seg_op("ds");
    return "$op,hint_yes" if defined($op) && $op =~ /^j[^m]/;
    return $op;
  }
  elsif ($byte == 0x3f) { return "aas" }
  elsif ($byte >= 0x40 && $byte <= 0x47) {
    return $self->op_reg("inc", $byte);
  }
  elsif ($byte >= 0x48 && $byte <= 0x4f) {
    return $self->op_reg("dec", $byte);
  }
  elsif ($byte >= 0x50 && $byte <= 0x57) {
    return $self->op_reg("push", $byte);
  }
  elsif ($byte >= 0x58 && $byte <= 0x5f) {
    return $self->op_reg("pop", $byte);
  }
  elsif ($byte == 0x60) {
    $self->{proc} = 186;
    return iflong($self, "pushad", "pusha");
  }
  elsif ($byte == 0x61) {
    $self->{proc} = 186;
    return iflong($self, "popad", "popa");
  }
  elsif ($byte == 0x62) {
    $self->{proc} = 186;
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $bound = $self->modrm($mod, $rm, "");
    return "bound $regs{$self->{data_size}}[$reg],$bound";
  }
  elsif ($byte == 0x63) {
    $self->{proc} = 286;
    return $self->op_rm_r("arpl", "word");
  }
  elsif ($byte == 0x64) { return $self->seg_op("fs", 386) }
  elsif ($byte == 0x65) { return $self->seg_op("gs", 386) }
  elsif ($byte == 0x66) {
    my $old_size = $self->{data_size};
    $self->{data_size} = toggle_size($old_size);
    $self->{mmx_pre} = 1;
    my $op = $self->_disasm();
    $self->{mmx_pre} = 0;
    $self->{data_size} = $old_size;
    $self->{proc} = 386 if $self->{proc} < 386;
    return $op;
  }
  elsif ($byte == 0x67) {
    my $old_size = $self->{addr_size};
    $self->{addr_size} = toggle_size($old_size);
    my $op = $self->_disasm();
    $self->{addr_size} = $old_size;
    $self->{proc} = 386 if $self->{proc} < 386;
    return $op;
  }
  elsif ($byte == 0x68) {
    $self->{proc} = 186;
    return sprintf "push %s(0x%x)", $self->{data_size}, $self->get_val();
  }
  elsif ($byte == 0x69) {
    $self->{proc} = 186;
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $src  = $self->modrm($mod, $rm);
    my $dest = $regs{$self->{data_size}}[$reg];
    return sprintf "imul %s,%s,0x%x", $dest, $src, $self->get_val();
  }
  elsif ($byte == 0x6a) {
    $self->{proc} = 186;
    return sprintf "push %s(0x%x)", $self->{data_size}, $self->get_byteval();
  }
  elsif ($byte == 0x6b) {
    $self->{proc} = 186;
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $src  = $self->modrm($mod, $rm);
    my $dest = $regs{$self->{data_size}}[$reg];
    return sprintf "imul %s,%s,0x%x", $dest, $src, $self->get_byteval();
  }
  elsif ($byte == 0x6c) {
    $self->{proc} = 186;
    my $dest = $self->string_edi("byte");
    return "ins $dest,byte[dx]";
  }
  elsif ($byte == 0x6d) {
    $self->{proc} = 186;
    my $dest = $self->string_edi();
    return "ins $dest,$self->{data_size}\[dx]";
  }
  elsif ($byte == 0x6e) {
    $self->{proc} = 186;
    my $src = $self->string_esi("byte");
    return "outs byte[dx],$src";
  }
  elsif ($byte == 0x6f) {
    $self->{proc} = 186;
    my $src = $self->string_esi();
    return "outs $self->{data_size}\[dx],$src";
  }
  elsif ($byte >= 0x70 && $byte <= 0x7f) {
    return sprintf "j%s 0x%x", $cond_code[$byte & 0xf], $self->eip_byteoff();
  }
  elsif ($byte == 0x80 || $byte == 0x82) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm, "byte");
    return sprintf "%s %s,0x%x", $immed_grp[$op], $dest, $self->next_byte();
  }
  elsif ($byte == 0x81) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return sprintf "%s %s,0x%x", $immed_grp[$op], $dest, $self->get_val();
  }
  elsif ($byte == 0x83) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return sprintf "%s %s,0x%x", $immed_grp[$op], $dest, $self->get_byteval();
  }
  elsif ($byte == 0x84) { return $self->op_rm_r("test", "byte") }
  elsif ($byte == 0x85) { return $self->op_rm_r("test") }
  elsif ($byte == 0x86) { return $self->op_r_rm("xchg", "byte") }
  elsif ($byte == 0x87) { return $self->op_r_rm("xchg") }
  elsif ($byte >= 0x88 && $byte <= 0x8b) {
    return $self->arith_op("mov", $byte);
  }
  elsif ($byte == 0x8c) {
    my ($mod, $seg, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $seg <= 5;
    return "mov " . $self->modrm($mod, $rm, "word") . ",$segregs[$seg]";
  }
  elsif ($byte == 0x8d) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $arg = $self->modrm($mod, $rm, "");
    return "lea $regs{$self->{data_size}}[$reg],$arg";
  }
  elsif ($byte == 0x8e) {
    my ($mod, $seg, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $seg <= 5;
    return "mov $segregs[$seg]," . $self->modrm($mod, $rm, "word");
  }
  elsif ($byte == 0x8f) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    return "pop " . $self->modrm($mod, $rm);
  }
  elsif ($byte == 0x90) {
    my $mmx_pre = $self->mmx_prefix();
    return "nop"   if $mmx_pre == 0;
    return "pause" if $mmx_pre == 3;
    return $self->bad_op();
  }
  elsif ($byte >= 0x91 && $byte <= 0x97) {
    my $e = iflong($self,"e","");
    my $reg = $regs{$self->{data_size}}[$byte & 7];
    return "xchg ${e}ax,$reg";
  }
  elsif ($byte == 0x98) { return iflong($self, "cwde", "cbw") }
  elsif ($byte == 0x99) { return iflong($self, "cdq", "cwd") }
  elsif ($byte == 0x9a) {
    my $off = $self->get_val();
    my $seg = $self->next_word();
    return sprintf "call 0x%x:0x%x", $seg, $off;
  }
  elsif ($byte == 0x9b) { $self->{proc} = 87; return "fwait" }
  elsif ($byte == 0x9c) { return iflong($self, "pushfd", "pushf") }
  elsif ($byte == 0x9d) { return iflong($self, "popfd", "popf") }
  elsif ($byte == 0x9e) { return "sahf" }
  elsif ($byte == 0x9f) { return "lahf" }
  elsif ($byte == 0xa0) { return "mov al," . $self->abs_addr("byte") }
  elsif ($byte == 0xa1) {
    my $e = iflong($self,"e","");
    return "mov ${e}ax," . $self->abs_addr();
  }
  elsif ($byte == 0xa2) {
    return "mov " . $self->abs_addr("byte") . ",al"
  }
  elsif ($byte == 0xa3) {
    my $e = iflong($self,"e","");
    return "mov " . $self->abs_addr() . ",${e}ax";
  }
  elsif ($byte == 0xa4) {
    my $src  = $self->string_esi("byte");
    my $dest = $self->string_edi("byte");
    return "movs $dest,$src";
  }
  elsif ($byte == 0xa5) {
    my $src  = $self->string_esi();
    my $dest = $self->string_edi();
    return "movs $dest,$src";
  }
  elsif ($byte == 0xa6) {
    my $src  = $self->string_esi("byte");
    my $dest = $self->string_edi("byte");
    return "cmps $src,$dest";
  }
  elsif ($byte == 0xa7) {
    my $src  = $self->string_esi();
    my $dest = $self->string_edi();
    return "cmps $src,$dest";
  }
  elsif ($byte == 0xa8) {
    return sprintf "test al,0x%x", $self->next_byte();
  }
  elsif ($byte == 0xa9) {
    return sprintf "test %sax,0x%x", iflong($self,"e",""), $self->get_val();
  }
  elsif ($byte == 0xaa) {
    my $dest = $self->string_edi("byte");
    return "stos $dest,al";
  }
  elsif ($byte == 0xab) {
    my $dest = $self->string_edi();
    my $e = iflong($self,"e","");
    return "stos $dest,${e}ax";
  }
  elsif ($byte == 0xac) {
    my $src = $self->string_esi("byte");
    return "lods al,$src";
  }
  elsif ($byte == 0xad) {
    my $src = $self->string_esi();
    my $e = iflong($self,"e","");
    return "lods ${e}ax,$src";
  }
  elsif ($byte == 0xae) {
    my $dest = $self->string_edi("byte");
    return "scas al,$dest";
  }
  elsif ($byte == 0xaf) {
    my $dest = $self->string_edi();
    my $e = iflong($self,"e","");
    return "scas ${e}ax,$dest";
  }
  elsif ($byte >= 0xb0 && $byte <= 0xb7) {
    my $dest = $byteregs[$byte & 7];
    return sprintf "mov %s,0x%x", $dest, $self->next_byte();
  }
  elsif ($byte >= 0xb8 && $byte <= 0xbf) {
    my $dest = $regs{$self->{data_size}}[$byte & 7];
    return sprintf "mov %s,0x%x", $dest, $self->get_val();
  }
  elsif ($byte == 0xc0) { return $self->shift_imm("byte") }
  elsif ($byte == 0xc1) { return $self->shift_imm() }
  elsif ($byte == 0xc2) { return sprintf "ret 0x%x", $self->next_word() }
  elsif ($byte == 0xc3) { return "ret" }
  elsif ($byte == 0xc4) { return $self->load_far("es") }
  elsif ($byte == 0xc5) { return $self->load_far("ds") }
  elsif ($byte == 0xc6) { return $self->mov_imm("byte") }
  elsif ($byte == 0xc7) { return $self->mov_imm() }
  elsif ($byte == 0xc8) {
    $self->{proc} = 186;
    my $immw = $self->next_word();
    my $immb = $self->next_byte();
    return sprintf "enter 0x%x,0x%x", $immw, $immb;
  }
  elsif ($byte == 0xc9) { $self->{proc} = 186; return "leave" }
  elsif ($byte == 0xca) { return sprintf "retf 0x%x", $self->next_word() }
  elsif ($byte == 0xcb) { return "retf" }
  elsif ($byte == 0xcc) { return "int 0x3" }
  elsif ($byte == 0xcd) { return sprintf "int 0x%x", $self->next_byte() }
  elsif ($byte == 0xce) { return "into" }
  elsif ($byte == 0xcf) { return iflong($self, "iretd", "iret") }
  elsif ($byte == 0xd0) { return $self->shift_op("0x1", "byte") }
  elsif ($byte == 0xd1) { return $self->shift_op("0x1") }
  elsif ($byte == 0xd2) { return $self->shift_op("cl", "byte") }
  elsif ($byte == 0xd3) { return $self->shift_op("cl") }
  elsif ($byte == 0xd4) { return sprintf "aam 0x%x", $self->next_byte() }
  elsif ($byte == 0xd5) { return sprintf "aad 0x%x", $self->next_byte() }
  elsif ($byte == 0xd6) { return $self->bad_op() }
  elsif ($byte == 0xd7) {
    my $e = $self->{addr_size} eq "dword" ? "e" : "";
    return "xlat al,byte[$self->{seg_reg}${e}bx+al]";
  }
  elsif ($byte == 0xd8) { return $self->escape_d8() }
  elsif ($byte == 0xd9) { return $self->escape_d9() }
  elsif ($byte == 0xda) { return $self->escape_da() }
  elsif ($byte == 0xdb) { return $self->escape_db() }
  elsif ($byte == 0xdc) { return $self->escape_dc() }
  elsif ($byte == 0xdd) { return $self->escape_dd() }
  elsif ($byte == 0xde) { return $self->escape_de() }
  elsif ($byte == 0xdf) { return $self->escape_df() }
  elsif ($byte == 0xe0) { return sprintf "loopnz 0x%x", $self->eip_byteoff() }
  elsif ($byte == 0xe1) { return sprintf "loopz 0x%x", $self->eip_byteoff() }
  elsif ($byte == 0xe2) { return sprintf "loop 0x%x", $self->eip_byteoff() }
  elsif ($byte == 0xe3) {
    return sprintf "j%scxz 0x%x", iflong($self,"e",""), $self->eip_byteoff();
  }
  elsif ($byte == 0xe4) {
    return sprintf "in al,byte[0x%x]", $self->next_byte()
  }
  elsif ($byte == 0xe5) {
    my $size = $self->{data_size};
    return sprintf "in %sax,%s[0x%x]", iflong($self,"e",""),
        $self->{data_size}, $self->next_byte();
  }
  elsif ($byte == 0xe6) {
    return sprintf "out byte[0x%x],al", $self->next_byte();
  }
  elsif ($byte == 0xe7) {
    return sprintf "out %s[0x%x],%sax", $self->{data_size},
        $self->next_byte(), iflong($self,"e","");
  }
  elsif ($byte == 0xe8) { return sprintf "call 0x%x", $self->eip_off() }
  elsif ($byte == 0xe9) { return sprintf "jmp 0x%x", $self->eip_off() }
  elsif ($byte == 0xea) {
    my $off = $self->get_val();
    my $seg = $self->next_word();
    return sprintf "jmp 0x%x:0x%x", $seg, $off;
  }
  elsif ($byte == 0xeb) { return sprintf "jmp 0x%x", $self->eip_byteoff() }
  elsif ($byte == 0xec) { return "in al,byte[dx]" }
  elsif ($byte == 0xed) {
    my $e = iflong($self,"e","");
    return "in ${e}ax,$self->{data_size}\[dx]";
  }
  elsif ($byte == 0xee) { return "out byte[dx],al" }
  elsif ($byte == 0xef) {
    my $e = iflong($self,"e","");
    return "out $self->{data_size}\[dx],${e}ax";
  }
  elsif ($byte == 0xf0) {
    my $op = $self->_disasm();
    return undef unless defined $op;
    return "lock $op";
  }
  elsif ($byte == 0xf1) { return $self->bad_op() }
  elsif ($byte == 0xf2) {
    $self->{mmx_pre} = 2;
    my $op = $self->_disasm();
    return $op unless $self->mmx_prefix() && defined $op;
    return "repnz $op";
  }
  elsif ($byte == 0xf3) {
    $self->{mmx_pre} = 3;
    my $op = $self->_disasm();
    return $op unless $self->mmx_prefix() && defined $op;
    return "repz $op" if $op =~ /^cmps/ || $op =~ /^scas/;
    return "rep $op";
  }
  elsif ($byte == 0xf4) { return "hlt" }
  elsif ($byte == 0xf5) { return "cmc" }
  elsif ($byte == 0xf6) { return $self->unary_op("byte") }
  elsif ($byte == 0xf7) { return $self->unary_op() }
  elsif ($byte == 0xf8) { return "clc" }
  elsif ($byte == 0xf9) { return "stc" }
  elsif ($byte == 0xfa) { return "cli" }
  elsif ($byte == 0xfb) { return "sti" }
  elsif ($byte == 0xfc) { return "cld" }
  elsif ($byte == 0xfd) { return "std" }
  elsif ($byte == 0xfe) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    if    ($op == 0) { return "inc " . $self->modrm($mod, $rm, "byte") }
    elsif ($op == 1) { return "dec " . $self->modrm($mod, $rm, "byte") }
    return $self->bad_op();
  }
  elsif ($byte == 0xff) { return $self->opgrp_ff() }
  die "can't happen";
} # _disasm

sub twobyte {
  my ($self) = @_;
  my $byte = $self->next_byte();
  my $old_proc = $self->{proc};
  $self->{proc} = 386;
  if ($byte == 0x00) { return $self->twobyte_00() }
  elsif ($byte == 0x01) {
    $self->{proc} = $old_proc;
    return $self->twobyte_01();
  }
  elsif ($byte == 0x02) { return $self->op_r_rm("lar") }
  elsif ($byte == 0x03) { return $self->op_r_rm("lsl") }
  elsif ($byte == 0x06) { return "clts" }
  elsif ($byte == 0x08) { $self->{proc} = 486; return "invd" }
  elsif ($byte == 0x09) { $self->{proc} = 486; return "wbinvd" }
  elsif ($byte == 0x0b) { $self->{proc} = 686; return "ud2" }
  elsif ($byte == 0x0d) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    my $arg = $self->modrm($mod, $rm, "");
    $self->{proc} = $tdnow_proc;
    if    ($op == 0) { return "prefetch $arg"  }
    elsif ($op == 1) { return "prefetchw $arg" }
    return $self->bad_op();
  }
  elsif ($byte == 0x0e) { $self->{proc} = $tdnow_proc; return "femms" }
  elsif ($byte == 0x0f) { return $self->tdnow_op() }
  elsif ($byte == 0x10) { return $self->twobyte_10() }
  elsif ($byte == 0x11) { return $self->twobyte_10(1) }
  elsif ($byte == 0x12) { return $self->twobyte_12("l") }
  elsif ($byte == 0x13) { return $self->twobyte_12("l", 1) }
  elsif ($byte == 0x14) { return $self->sse_op2("unpcklp") }
  elsif ($byte == 0x15) { return $self->sse_op2("unpckhp") }
  elsif ($byte == 0x16) { return $self->twobyte_12("h") }
  elsif ($byte == 0x17) { return $self->twobyte_12("h", 1) }
  elsif ($byte == 0x18) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    return $self->bad_op() if $mod == 3 || $op > 3;
    $self->{proc} = $sse_proc;
    return "prefetch$prefetch_op[$op] " . $self->modrm($mod, $rm, "");
  }
  elsif ($byte == 0x20) {
    my ($mod, $cr, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $mod == 3;
    return "mov $longregs[$rm],cr$cr";
  }
  elsif ($byte == 0x21) {
    my ($mod, $dr, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $mod == 3;
    return "mov $longregs[$rm],dr$dr";
  }
  elsif ($byte == 0x22) {
    my ($mod, $cr, $rm) = $self->split_next_byte;
    return $self->bad_op() unless $mod == 3;
    return "mov cr$cr,$longregs[$rm]";
  }
  elsif ($byte == 0x23) {
    my ($mod, $dr, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $mod == 3;
    return "mov dr$dr,$longregs[$rm]";
  }
  elsif ($byte == 0x24) {
    my ($mod, $tr, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $mod == 3;
    return "mov $longregs[$rm],tr$tr";
  }
  elsif ($byte == 0x26) {
    my ($mod, $tr, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $mod == 3;
    return "mov tr$tr,$longregs[$rm]";
  }
  elsif ($byte == 0x28) { return $self->sse_op2("movap") }
  elsif ($byte == 0x29) { return $self->twobyte_29() }
  elsif ($byte == 0x2a) { return $self->twobyte_2a() }
  elsif ($byte == 0x2b) { return $self->twobyte_2b() }
  elsif ($byte == 0x2c) { return $self->twobyte_2c("t") }
  elsif ($byte == 0x2d) { return $self->twobyte_2c("") }
  elsif ($byte == 0x2e) { return $self->twobyte_2e("ucomis") }
  elsif ($byte == 0x2f) { return $self->twobyte_2e("comis") }
  elsif ($byte == 0x30) { $self->{proc} = 586; return "wrmsr" }
  elsif ($byte == 0x31) { $self->{proc} = 586; return "rdtsc" }
  elsif ($byte == 0x32) { $self->{proc} = 586; return "rdmsr" }
  elsif ($byte == 0x33) { $self->{proc} = 686; return "rdpmc" }
  elsif ($byte == 0x34) { $self->{proc} = 686; return "sysenter" }
  elsif ($byte == 0x35) { $self->{proc} = 686; return "sysexit" }
  elsif ($byte >= 0x40 && $byte <= 0x4f) {
    $self->{proc} = 686;
    return $self->op_r_rm("cmov" . $cond_code[$byte & 0xf]);
  }
  elsif ($byte == 0x50) { return $self->twobyte_50() }
  elsif ($byte == 0x51) { return $self->sse_op4("sqrt") }
  elsif ($byte == 0x52) { return $self->twobyte_52("rsqrt") }
  elsif ($byte == 0x53) { return $self->twobyte_52("rcp") }
  elsif ($byte == 0x54) { return $self->sse_op2("andp") }
  elsif ($byte == 0x55) { return $self->sse_op2("andnp") }
  elsif ($byte == 0x56) { return $self->sse_op2("orp") }
  elsif ($byte == 0x57) { return $self->sse_op2("xorp") }
  elsif ($byte == 0x58) { return $self->sse_op4("add") }
  elsif ($byte == 0x59) { return $self->sse_op4("mul") }
  elsif ($byte == 0x5a) { return $self->twobyte_5a() }
  elsif ($byte == 0x5b) { return $self->twobyte_5b() }
  elsif ($byte == 0x5c) { return $self->sse_op4("sub") }
  elsif ($byte == 0x5d) { return $self->sse_op4("min") }
  elsif ($byte == 0x5e) { return $self->sse_op4("div") }
  elsif ($byte == 0x5f) { return $self->sse_op4("max") }
  elsif ($byte == 0x60) { return $self->mmx_op("punpcklbw") }
  elsif ($byte == 0x61) { return $self->mmx_op("punpcklwd") }
  elsif ($byte == 0x62) { return $self->mmx_op("punpckldq") }
  elsif ($byte == 0x63) { return $self->mmx_op("packsswb") }
  elsif ($byte == 0x64) { return $self->mmx_op("pcmpgtb") }
  elsif ($byte == 0x65) { return $self->mmx_op("pcmpgtw") }
  elsif ($byte == 0x66) { return $self->mmx_op("pcmpgtd") }
  elsif ($byte == 0x67) { return $self->mmx_op("packuswb") }
  elsif ($byte == 0x68) { return $self->mmx_op("punpckhbw") }
  elsif ($byte == 0x69) { return $self->mmx_op("punpckhwd") }
  elsif ($byte == 0x6a) { return $self->mmx_op("punpckhdq") }
  elsif ($byte == 0x6b) { return $self->mmx_op("packssdw") }
  elsif ($byte == 0x6c) { return $self->twobyte_6c("punpcklqdq") }
  elsif ($byte == 0x6d) { return $self->twobyte_6c("punpckhqdq") }
  elsif ($byte == 0x6e) { return $self->twobyte_6e() }
  elsif ($byte == 0x6f) { return $self->twobyte_6f() }
  elsif ($byte == 0x70) { return $self->twobyte_70() }
  elsif ($byte == 0x71) { return $self->twobyte_71("w") }
  elsif ($byte == 0x72) { return $self->twobyte_71("d") }
  elsif ($byte == 0x73) { return $self->twobyte_73() }
  elsif ($byte == 0x74) { return $self->mmx_op("pcmpeqb") }
  elsif ($byte == 0x75) { return $self->mmx_op("pcmpeqw") }
  elsif ($byte == 0x76) { return $self->mmx_op("pcmpeqd") }
  elsif ($byte == 0x77) { $self->{proc} = $mmx_proc; return "emms" }
  elsif ($byte == 0x7e) { return $self->twobyte_7e() }
  elsif ($byte == 0x7f) { return $self->twobyte_7f() }
  elsif ($byte >= 0x80 && $byte <= 0x8f) {
    return sprintf "j%s 0x%x", $cond_code[$byte & 0xf], $self->eip_off();
  }
  elsif ($byte >= 0x90 && $byte <= 0x9f) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm, "byte");
    return "set$cond_code[$byte&0xf] $dest";
  }
  elsif ($byte == 0xa0) { return "push fs" }
  elsif ($byte == 0xa1) { return "pop fs" }
  elsif ($byte == 0xa2) { $self->{proc} = 486; return "cpuid" }
  elsif ($byte == 0xa3) { return $self->op_rm_r("bt") }
  elsif ($byte == 0xa4) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return sprintf "shld %s,%s,0x%x", $dest,
        $regs{$self->{data_size}}[$reg], $self->next_byte();
  }
  elsif ($byte == 0xa5) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return sprintf "shld %s,%s,cl", $dest, $regs{$self->{data_size}}[$reg];
  }
  elsif ($byte == 0xa8) { return "push gs" }
  elsif ($byte == 0xa9) { return "pop gs" }
  elsif ($byte == 0xaa) { return "rsm" }
  elsif ($byte == 0xab) { return $self->op_rm_r("bts") }
  elsif ($byte == 0xac) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return sprintf "shrd %s,%s,0x%x", $dest,
        $regs{$self->{data_size}}[$reg], $self->next_byte();
  }
  elsif ($byte == 0xad) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return sprintf "shrd %s,%s,cl", $dest, $regs{$self->{data_size}}[$reg];
  }
  elsif ($byte == 0xae) { return $self->twobyte_ae() }
  elsif ($byte == 0xaf) { return $self->op_r_rm("imul") }
  elsif ($byte == 0xb0) {
    $self->{proc} = 486;
    return $self->op_rm_r("cmpxchg", "byte");
  }
  elsif ($byte == 0xb1) {
    $self->{proc} = 486;
    return $self->op_rm_r("cmpxchg");
  }
  elsif ($byte == 0xb2) { return $self->load_far("ss") }
  elsif ($byte == 0xb3) { return $self->op_rm_r("btr") }
  elsif ($byte == 0xb4) { return $self->load_far("fs") }
  elsif ($byte == 0xb5) { return $self->load_far("gs") }
  elsif ($byte == 0xb6) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $src = $self->modrm($mod, $rm, "byte");
    return "movzx $regs{$self->{data_size}}[$reg],$src";
  }
  elsif ($byte == 0xb7) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    return "movzx $longregs[$reg]," . $self->modrm($mod, $rm, "word");
  }
  elsif ($byte == 0xba) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $op >= 4;
    my $dest = $self->modrm($mod, $rm);
    return sprintf "%s %s,0x%x", $bittst_grp[$op - 4], $dest,
        $self->next_byte();
  }
  elsif ($byte == 0xbb) { return $self->op_rm_r("btc") }
  elsif ($byte == 0xbc) { return $self->op_r_rm("bsf") }
  elsif ($byte == 0xbd) { return $self->op_r_rm("bsr") }
  elsif ($byte == 0xbe) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $src = $self->modrm($mod, $rm, "byte");
    return "movsx $regs{$self->{data_size}}[$reg],$src";
  }
  elsif ($byte == 0xbf) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    return "movsx $longregs[$reg]," . $self->modrm($mod, $rm, "word");
  }
  elsif ($byte == 0xc0) {
    $self->{proc} = 486;
    return $self->op_rm_r("xadd", "byte");
  }
  elsif ($byte == 0xc1) {
    $self->{proc} = 486;
    return $self->op_rm_r("xadd");
  }
  elsif ($byte == 0xc2) { return $self->twobyte_c2() }
  elsif ($byte == 0xc3) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    return $self->bad_op() if $mod == 3;
    $self->{proc} = $sse2_proc;
    my $mem = $self->modrm($mod, $rm, "dword");
    return "movnti $mem,$longregs[$reg]";
  }
  elsif ($byte == 0xc4) { return $self->twobyte_c4() }
  elsif ($byte == 0xc5) { return $self->twobyte_c5() }
  elsif ($byte == 0xc6) { return $self->twobyte_c6() }
  elsif ($byte == 0xc7) {
    my ($mod, $op, $rm) = $self->split_next_byte();
    return $self->bad_op() unless $op == 1;
    $self->{proc} = 586;
    return $self->bad_op() if $mod == 3;
    return "cmpxchg8b " . $self->modrm($mod, $rm, "qword");
  }
  elsif ($byte >= 0xc8 && $byte <= 0xcf) {
    $self->{proc} = 486;
    return "bswap $longregs[$byte&7]";
  }
  elsif ($byte == 0xd1) { return $self->mmx_op("psrlw") }
  elsif ($byte == 0xd2) { return $self->mmx_op("psrld") }
  elsif ($byte == 0xd3) { return $self->mmx_op("psrlq") }
  elsif ($byte == 0xd4) { return $self->mmx_op("paddq", $sse2_proc) }
  elsif ($byte == 0xd5) { return $self->mmx_op("pmullw") }
  elsif ($byte == 0xd6) { return $self->twobyte_d6() }
  elsif ($byte == 0xd7) { return $self->twobyte_d7() }
  elsif ($byte == 0xd8) { return $self->mmx_op("psubusb") }
  elsif ($byte == 0xd9) { return $self->mmx_op("psubusw") }
  elsif ($byte == 0xda) { return $self->mmx_op("pminub", $sse_proc) }
  elsif ($byte == 0xdb) { return $self->mmx_op("pand") }
  elsif ($byte == 0xdc) { return $self->mmx_op("paddusb") }
  elsif ($byte == 0xdd) { return $self->mmx_op("paddusw") }
  elsif ($byte == 0xde) { return $self->mmx_op("pmaxub", $sse_proc) }
  elsif ($byte == 0xdf) { return $self->mmx_op("pandn") }
  elsif ($byte == 0xe0) { return $self->mmx_op("pavgb", $sse_proc) }
  elsif ($byte == 0xe1) { return $self->mmx_op("psraw") }
  elsif ($byte == 0xe2) { return $self->mmx_op("psrad") }
  elsif ($byte == 0xe3) { return $self->mmx_op("pavgw", $sse_proc) }
  elsif ($byte == 0xe4) { return $self->mmx_op("pmulhuw", $sse_proc) }
  elsif ($byte == 0xe5) { return $self->mmx_op("pmulhw") }
  elsif ($byte == 0xe6) { return $self->twobyte_e6() }
  elsif ($byte == 0xe7) { return $self->twobyte_e7() }
  elsif ($byte == 0xe8) { return $self->mmx_op("psubsb") }
  elsif ($byte == 0xe9) { return $self->mmx_op("psubsw") }
  elsif ($byte == 0xea) { return $self->mmx_op("pminsw", $sse_proc) }
  elsif ($byte == 0xeb) { return $self->mmx_op("por") }
  elsif ($byte == 0xec) { return $self->mmx_op("paddsb") }
  elsif ($byte == 0xed) { return $self->mmx_op("paddsw") }
  elsif ($byte == 0xee) { return $self->mmx_op("pmaxsw", $sse_proc) }
  elsif ($byte == 0xef) { return $self->mmx_op("pxor") }
  elsif ($byte == 0xf1) { return $self->mmx_op("psllw") }
  elsif ($byte == 0xf2) { return $self->mmx_op("pslld") }
  elsif ($byte == 0xf3) { return $self->mmx_op("psllq") }
  elsif ($byte == 0xf4) { return $self->mmx_op("pmuludq", $sse2_proc) }
  elsif ($byte == 0xf5) { return $self->mmx_op("pmaddwd") }
  elsif ($byte == 0xf6) { return $self->mmx_op("psadbw", $sse_proc) }
  elsif ($byte == 0xf7) { return $self->twobyte_f7() }
  elsif ($byte == 0xf8) { return $self->mmx_op("psubb") }
  elsif ($byte == 0xf9) { return $self->mmx_op("psubw") }
  elsif ($byte == 0xfa) { return $self->mmx_op("psubd") }
  elsif ($byte == 0xfb) { return $self->mmx_op("psubq", $sse2_proc) }
  elsif ($byte == 0xfc) { return $self->mmx_op("paddb") }
  elsif ($byte == 0xfd) { return $self->mmx_op("paddw") }
  elsif ($byte == 0xfe) { return $self->mmx_op("paddd") }
  return $self->bad_op();
} # twobyte

sub tdnow_op {
  my ($self) = @_;
  $self->{proc} = $tdnow_proc;
  my ($mod, $reg, $rm) = $self->split_next_byte();
  my $arg = $self->modrm($mod, $rm, "qword");
  my $byte = $self->next_byte();
  if    ($byte == 0x0d) { return "pi2fd mm$reg,$arg" }
  elsif ($byte == 0x1d) { return "pf2id mm$reg,$arg" }
  elsif ($byte == 0x90) { return "pfcmpge mm$reg,$arg" }
  elsif ($byte == 0x94) { return "pfmin mm$reg,$arg" }
  elsif ($byte == 0x96) { return "pfrcp mm$reg,$arg" }
  elsif ($byte == 0x97) { return "pfrsqrt mm$reg,$arg" }
  elsif ($byte == 0x9a) { return "pfsub mm$reg,$arg" }
  elsif ($byte == 0x9e) { return "pfadd mm$reg,$arg" }
  elsif ($byte == 0xa0) { return "pfcmpgt mm$reg,$arg" }
  elsif ($byte == 0xa4) { return "pfmax mm$reg,$arg" }
  elsif ($byte == 0xa6) { return "pfrcpit1 mm$reg,$arg" }
  elsif ($byte == 0xa7) { return "pfrsqit1 mm$reg,$arg" }
  elsif ($byte == 0xaa) { return "pfsubr mm$reg,$arg" }
  elsif ($byte == 0xae) { return "pfacc mm$reg,$arg" }
  elsif ($byte == 0xb0) { return "pfcmpeq mm$reg,$arg" }
  elsif ($byte == 0xb4) { return "pfmul mm$reg,$arg" }
  elsif ($byte == 0xb6) { return "pfrcpit2 mm$reg,$arg" }
  elsif ($byte == 0xb7) { return "pmulhrw mm$reg,$arg" }
  elsif ($byte == 0xbf) { return "pavgusb mm$reg,$arg" }
  elsif ($byte == 0x0c) {
    $self->{proc} = $tdnow2_proc;
    return "pi2fw mm$reg,$arg";
  }
  elsif ($byte == 0x1c) {
    $self->{proc} = $tdnow2_proc;
    return "pf2iw mm$reg,$arg";
  }
  elsif ($byte == 0x8a) {
    $self->{proc} = $tdnow2_proc;
    return "pfnacc mm$reg,$arg";
  }
  elsif ($byte == 0x8e) {
    $self->{proc} = $tdnow2_proc;
    return "pfpnacc mm$reg,$arg";
  }
  elsif ($byte == 0xbb) {
    $self->{proc} = $tdnow2_proc;
    return "pswapd mm$reg,$arg";
  }
  return $self->bad_op();
} # tdnow_op

sub escape_d8 {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  return "f$float_op[$op] st0,st$rm" if $mod == 3;
  return "f$float_op[$op] st0," . $self->modrm($mod, $rm, "dword");
} # escape_d8

sub escape_d9 {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod != 3) {
    if    ($op == 0) { return "fld "    . $self->modrm($mod, $rm, "dword") }
    elsif ($op == 2) { return "fst "    . $self->modrm($mod, $rm, "dword") }
    elsif ($op == 3) { return "fstp "   . $self->modrm($mod, $rm, "dword") }
    elsif ($op == 4) { return "fldenv " . $self->modrm($mod, $rm, "")      }
    elsif ($op == 5) { return "fldcw "  . $self->modrm($mod, $rm, "word")  }
    elsif ($op == 6) { return "fstenv " . $self->modrm($mod, $rm, "")      }
    elsif ($op == 7) { return "fstcw "  . $self->modrm($mod, $rm, "word")  }
  }
  elsif ($op == 0) { return "fld st$rm" }
  elsif ($op == 1) { return "fxch st0,st$rm" }
  elsif ($op == 2 && $rm == 0) { return "fnop" }
  elsif ($op == 4) {
    if    ($rm == 0) { return "fchs" }
    elsif ($rm == 1) { return "fabs" }
    elsif ($rm == 4) { return "ftst" }
    elsif ($rm == 5) { return "fxam" }
  }
  elsif ($op == 5) {
    if    ($rm == 0) { return "fld1" }
    elsif ($rm == 1) { return "fldl2t" }
    elsif ($rm == 2) { return "fldl2e" }
    elsif ($rm == 3) { return "fldpi" }
    elsif ($rm == 4) { return "fldlg2" }
    elsif ($rm == 5) { return "fldln2" }
    elsif ($rm == 6) { return "fldz" }
  }
  elsif ($op == 6) {
    if    ($rm == 0) { return "f2xm1" }
    elsif ($rm == 1) { return "fyl2x" }
    elsif ($rm == 2) { return "fptan" }
    elsif ($rm == 3) { return "fpatan" }
    elsif ($rm == 4) { return "fxtract" }
    elsif ($rm == 5) { $self->{proc} = 387; return "fprem1" }
    elsif ($rm == 6) { return "fdecstp" }
    elsif ($rm == 7) { return "fincstp" }
  }
  elsif ($op == 7) {
    if    ($rm == 0) { return "fprem" }
    elsif ($rm == 1) { return "fyl2xp1" }
    elsif ($rm == 2) { return "fsqrt" }
    elsif ($rm == 3) { $self->{proc} = 387; return "fsincos" }
    elsif ($rm == 4) { return "frndint" }
    elsif ($rm == 5) { return "fscale" }
    elsif ($rm == 6) { $self->{proc} = 387; return "fsin" }
    elsif ($rm == 7) { $self->{proc} = 387; return "fcos" }
  }
  return $self->bad_op();
} # escape_d9

sub escape_da {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod != 3) {
    return "fi$float_op[$op] st0," . $self->modrm($mod, $rm, "dword");
  }
  elsif ($op == 0) { $self->{proc} = 686; return "fcmovb st0,st$rm"  }
  elsif ($op == 1) { $self->{proc} = 686; return "fcmove st0,st$rm"  }
  elsif ($op == 2) { $self->{proc} = 686; return "fcmovbe st0,st$rm" }
  elsif ($op == 3) { $self->{proc} = 686; return "fcmovu st0,st$rm"  }
  elsif ($op == 5 && $rm == 1) { $self->{proc} = 387; return "fucompp" }
  return $self->bad_op();
} # escape_da

sub escape_db {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod == 3) {
    if    ($op == 0) { $self->{proc} = 686; return "fcmovnb st0,st$rm"  }
    elsif ($op == 1) { $self->{proc} = 686; return "fcmovne st0,st$rm"  }
    elsif ($op == 2) { $self->{proc} = 686; return "fcmovnbe st0,st$rm" }
    elsif ($op == 3) { $self->{proc} = 686; return "fcmovnbu st0,st$rm" }
    elsif ($op == 4 && $rm == 2) { return "fnclex" }
    elsif ($op == 4 && $rm == 3) { return "fninit"  }
    elsif ($op == 5) { $self->{proc} = 686; return "fucomi st0,st$rm" }
    elsif ($op == 6) { $self->{proc} = 686; return "fcomi st0,st$rm"  }
  }
  elsif ($op == 0) { return "fild "  . $self->modrm($mod, $rm, "dword") }
  elsif ($op == 2) { return "fist "  . $self->modrm($mod, $rm, "dword") }
  elsif ($op == 3) { return "fistp " . $self->modrm($mod, $rm, "dword") }
  elsif ($op == 5) { return "fld "   . $self->modrm($mod, $rm, "tbyte") }
  elsif ($op == 7) { return "fstp "  . $self->modrm($mod, $rm, "tbyte") }
  return $self->bad_op();
} # escape_db

sub escape_dc {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod != 3) {
    return "f$float_op[$op] st0," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($op != 2 && $op != 3) {
    return "f$float_op[$op] st$rm,st0";
  }
  return $self->bad_op();
} # esop_dc

sub escape_dd {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod == 3) {
    if    ($op == 0) { return "ffree st$rm" }
    elsif ($op == 2) { return "fst st$rm"   }
    elsif ($op == 3) { return "fstp st$rm"  }
    elsif ($op == 4) { $self->{proc} = 387; return "fucom st$rm"  }
    elsif ($op == 5) { $self->{proc} = 387; return "fucomp st$rm" }
  }
  elsif ($op == 0) { return "fld "    . $self->modrm($mod, $rm, "qword") }
  elsif ($op == 2) { return "fst "    . $self->modrm($mod, $rm, "qword") }
  elsif ($op == 3) { return "fstp "   . $self->modrm($mod, $rm, "qword") }
  elsif ($op == 4) { return "frstor " . $self->modrm($mod, $rm, "") }
  elsif ($op == 6) { return "fsave "  . $self->modrm($mod, $rm, "") }
  elsif ($op == 7) { return "fstsw "  . $self->modrm($mod, $rm, "word") }
  return $self->bad_op();
} # escape_dd

sub escape_de {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod != 3) {
    return "fi$float_op[$op] st0," . $self->modrm($mod, $rm, "word");
  }
  elsif ($op != 2 && $op != 3) {
    return "f$float_op[$op]p st$rm,st0";
  }
  elsif ($op == 3 && $rm == 1) { return "fcompp" }
  return $self->bad_op();
} # escape_de

sub escape_df {
  my ($self) = @_;
  $self->{proc} = 87;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod == 3) {
    if ($op == 4 && $rm == 0) { return "fnstsw ax" }
    elsif ($op == 5) { return "fucomip st0,st$rm" }
    elsif ($op == 6) { return "fcomip st0,st$rm"  }
  }
  elsif ($op == 0) { return "fild "  . $self->modrm($mod, $rm, "word")  }
  elsif ($op == 2) { return "fist "  . $self->modrm($mod, $rm, "word")  }
  elsif ($op == 3) { return "fistp " . $self->modrm($mod, $rm, "word")  }
  elsif ($op == 4) { return "fbld "  . $self->modrm($mod, $rm, "tbyte") }
  elsif ($op == 5) { return "fild "  . $self->modrm($mod, $rm, "qword") }
  elsif ($op == 6) { return "fbstp " . $self->modrm($mod, $rm, "tbyte") }
  elsif ($op == 7) { return "fistp " . $self->modrm($mod, $rm, "qword") }
  return $self->bad_op();
} # escape_df

sub opgrp_ff {
  my ($self) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if    ($op == 0) { return "inc " . $self->modrm($mod, $rm) }
  elsif ($op == 1) { return "dec " . $self->modrm($mod, $rm) }
  elsif ($op == 2) { return "call " . $self->modrm($mod, $rm) }
  elsif ($op == 3) {
    my $dest = $self->modrm($mod, $rm, iflong($self, "far32", "far"));
    return "call $dest";
  }
  elsif ($op == 4) { return "jmp " . $self->modrm($mod, $rm) }
  elsif ($op == 5) {
    my $dest = $self->modrm($mod, $rm, iflong($self, "far32", "far"));
    return "jmp $dest";
  }
  elsif ($op == 6) { return "push " . $self->modrm($mod, $rm) }
  return $self->bad_op();
} # opgrp_ff

sub twobyte_00 {
  my ($self) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if    ($op == 0) { return "sldt " . $self->modrm($mod, $rm) }
  my $arg = $self->modrm($mod, $rm, "word");
  if    ($op == 1) { return "str $arg"  }
  elsif ($op == 2) { return "lldt $arg" }
  elsif ($op == 3) { return "ltr $arg"  }
  elsif ($op == 4) { return "verr $arg" }
  elsif ($op == 5) { return "verw $arg" }
  return $self->bad_op();
} # twobyte_00

sub twobyte_01 {
  my ($self) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($op == 0) {
    $self->{proc} = 286;
    return "sgdt " . $self->modrm($mod, $rm, "");
  }
  elsif ($op == 1) {
    $self->{proc} = 286;
    return "sidt " . $self->modrm($mod, $rm, "");
  }
  elsif ($op == 2) {
    $self->{proc} = 386;
    return "lgdt " . $self->modrm($mod, $rm, "");
  }
  elsif ($op == 3) {
    $self->{proc} = 386;
    return "lidt " . $self->modrm($mod, $rm, "");
  }
  elsif ($op == 4) {
    $self->{proc} = 286;
    return "smsw " . $self->modrm($mod, $rm) if $mod == 3;
    return "smsw " . $self->modrm($mod, $rm, "word");
  }
  elsif ($op == 6) {
    $self->{proc} = 286;
    return "lmsw " . $self->modrm($mod, $rm, "word");
  }
  elsif ($op == 7) {
    $self->{proc} = 486;
    return "invlpg " . $self->modrm($mod, $rm, "");
  }
  return $self->bad_op();
} # twobyte_01

sub twobyte_10 {
  my ($self, $rev) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  my ($op, $arg);
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    $op = "movups";
    $arg = $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    $op = "movupd";
    $arg = $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    $op = "movsd";
    $arg = ($mod == 3) ? "xmm$rm" : $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 3) {
    $self->{proc} = $sse_proc;
    $op = "movss";
    $arg = ($mod == 3) ? "xmm$rm" : $self->modrm($mod, $rm, "dword");
  }
  else { return $self->bad_op() }
  return $rev ? "$op $arg,xmm$xmm" : "$op xmm$xmm,$arg";
} # twobyte_10

sub twobyte_12 {
  my ($self, $lh, $rev) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  $self->{proc} = $sse_proc;
  my $op;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    if ($mod == 3) {
      return $self->bad_op() if $rev;
      return "movhlps xmm$xmm,xmm$rm" if $lh eq "l";
      return "movlhps xmm$xmm,xmm$rm";
    }
    $op = "mov${lh}ps";
  }
  elsif ($mmx_pre == 1 && $mod != 3) { $op = "mov${lh}pd" }
  else { return $self->bad_op() }
  my $arg = $self->modrm($mod, $rm, "qword");
  return $rev ? "$op $arg,xmm$xmm" : "$op $xmm$xmm,$arg";
} # twobyte_12

sub twobyte_29 {
  my ($self, $op) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $dest = $self->modrm($mod, $rm, "dqword");
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "movaps $dest,xmm$xmm";
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    return "movapd $dest,xmm$xmm";
  }
  return $self->bad_op();
} # twobyte_29

sub twobyte_2a {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "cvtpi2ps xmm$xmm," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "cvtpi2pd xmm$xmm," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    return "cvtsi2sd xmm$xmm," . $self->modrm($mod, $rm, "dword");
  }
  elsif ($mmx_pre == 3) {
    $self->{proc} = $sse_proc;
    return "cvtsi2ss xmm$xmm," . $self->modrm($mod, $rm, "dword");
  }
  return $self->bad_op();
} # twobyte_2a

sub twobyte_2b {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  return $self->bad_op() if $mod == 3;
  my $dest = $self->modrm($mod, $rm, "dqword");
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "movntps $dest,xmm$xmm";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "movntpd $dest,xmm$xmm";
  }
  return $self->bad_op();
} # twobyte_2b

sub twobyte_2c {
  my ($self, $t) = @_;
  my ($mod, $reg, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "cvt${t}ps2pi mm$reg,xmm$rm" if $mod == 3;
    return "cvt${t}ps2pi mm$reg," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "cvt${t}pd2pi mm$reg," . $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    return "cvt${t}sd2si $longregs[$reg],xmm$rm" if $mod == 3;
    return "cvt${t}sd2si $longregs[$reg]," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 3) {
    $self->{proc} = $sse_proc;
    return "cvt${t}ss2si $longregs[$reg],xmm$rm" if $mod == 3;
    return "cvt${t}ss2si $longregs[$reg]," . $self->modrm($mod, $rm, "dword");
  }
  return $self->bad_op();
} # twobyte_2c

sub twobyte_2e {
  my ($self, $op) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "${op}s xmm$xmm,xmm$rm" if $mod == 3;
    return "${op}s xmm$xmm," . $self->modrm($mod, $rm, "dword");
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "${op}d xmm$xmm,xmm$rm" if $mod == 3;
    return "${op}d xmm$xmm," . $self->modrm($mod, $rm, "qword");
  }
  return $self->bad_op();
} # twobyte_2e

sub twobyte_50 {
  my ($self) = @_;
  my ($mod, $reg, $xmm) = $self->split_next_byte();
  return $self->bad_op() unless $mod == 3;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "movmskps $longregs[$reg],xmm$xmm";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "movmskpd $longregs[$reg],xmm$xmm";
  }
  return $self->bad_op();
} # twobyte_50

sub twobyte_52 {
  my ($self, $op) = @_;
  $self->{proc} = $sse_proc;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    return "${op}ps xmm$xmm," . $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 3) {
    return "${op}ss xmm$xmm,xmm$rm" if $mod == 3;
    return "${op}ss xmm$xmm," . $self->modrm($mod, $rm, "dword");
  }
  return $self->bad_op();
} # twobyte_52

sub twobyte_5a {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  $self->{proc} = $sse2_proc;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    return "cvtps2pd xmm$xmm,xmm$rm" if $mod == 3;
    return "cvtps2pd xmm$xmm," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 1) {
    return "cvtpd2ps xmm$xmm," . $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 2) {
    return "cvtsd2ss xmm$xmm,xmm$rm" if $mod == 3;
    return "cvtsd2ss xmm$xmm," . $self->modrm($mod, $rm, "qword");
  }
  elsif ($mmx_pre == 3) {
    return "cvtss2sd xmm$xmm,xmm$rm" if $mod == 3;
    return "cvtss2sd xmm$xmm," . $self->modrm($mod, $rm, "dword");
  }
  return $self->bad_op();
} # twobyte_5a

sub twobyte_5b {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  $self->{proc} = $sse2_proc;
  my $mmx_pre = $self->mmx_prefix();
  my $op;
  if    ($mmx_pre == 0) { $op = "cvtdq2ps"  }
  elsif ($mmx_pre == 1) { $op = "cvtps2dq"  }
  elsif ($mmx_pre == 3) { $op = "cvttps2dq" }
  else { return $self->bad_op() }
  return "$op xmm$xmm," . $self->modrm($mod, $rm, "dqword");
} # twobyte_5b

sub twobyte_6c {
  my ($self, $op) = @_;
  $self->{proc} = $sse2_proc;
  my $mmx_pre = $self->mmx_prefix();
  return $self->bad_op() unless $mmx_pre == 1;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $src = $self->modrm($mod, $rm, "dqword");
  return "$op xmm$xmm,$src";
} # twobyte_6c

sub twobyte_6e {
  my ($self) = @_;
  my ($mod, $mm, $rm) = $self->split_next_byte();
  my $src = $self->modrm($mod, $rm, "dword");
  my $mmx_pre = $self->mmx_prefix();
  if  ($mmx_pre == 0) {
    $self->{proc} = $mmx_proc;
    return "movd mm$mm,$src";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "movd xmm$mm,$src";
  }
  return $self->bad_op();
} # twobyte_6e

sub twobyte_6f {
  my ($self) = @_;
  my ($mod, $mm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $mmx_proc;
    my $src = $self->modrm($mod, $rm, "qword");
    return "movq mm$mm,$src";
  }
  $self->{proc} = $sse2_proc;
  my $src = $self->modrm($mod, $rm, "dqword");
  if ($mmx_pre == 1) { return "movdqa xmm$mm,$src" }
  elsif ($mmx_pre == 3) { return "movdqu xmm$mm,$src" }
  return $self->bad_op();
} # twobyte_6f

sub twobyte_70 {
  my ($self) = @_;
  my ($mod, $mm, $rm) = $self->split_next_byte;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    my $arg = $self->modrm($mod, $rm, "qword");
    return sprintf "pshufw mm%d,%s,0x%x", $mm, $arg, $self->next_byte();
  }
  $self->{proc} = $sse2_proc;
  my $arg = $self->modrm($mod, $rm, "dqword");
  my $op;
  if    ($mmx_pre == 1) { $op = "pshufd" }
  elsif ($mmx_pre == 2) { $op = "pshuflw" }
  elsif ($mmx_pre == 3) { $op = "pshufhw" }
  else { return $self->bad_op() }
  return sprintf "%s xmm%d,%s,0x%x", $op, $mm, $arg, $self->next_byte();
} # twobyte_70

sub twobyte_71 {
  my ($self, $size) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  return $self->bad_op() unless $mod == 3;
  if    ($op == 2) { return $self->mmx_shift_imm("psrl$size", $rm) }
  elsif ($op == 4) { return $self->mmx_shift_imm("psra$size", $rm) }
  elsif ($op == 6) { return $self->mmx_shift_imm("psll$size", $rm) }
  return $self->bad_op();
} # twobyte_71

sub twobyte_73 {
  my ($self) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  return $self->bad_op() unless $mod == 3;
  if    ($op == 2) { return $self->mmx_shift_imm("psrlq", $rm) }
  elsif ($op == 6) { return $self->mmx_shift_imm("psllq", $rm) }
  elsif ($op == 3 && $self->{mmx_pre}) {
    return $self->mmx_shift_imm("psrldq", $rm);
  }
  elsif ($op == 7 && $self->{mmx_pre}) {
    return $self->mmx_shift_imm("pslldq", $rm);
  }
  return $self->bad_op();
} # twobyte_73

sub twobyte_7e {
  my ($self) = @_;
  my ($mod, $mm, $rm) = $self->split_next_byte();
  my $dest = $self->modrm($mod, $rm, "dword");
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $mmx_proc;
    return "movd $dest,mm$mm";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "movd $dest,xmm$mm"
  }
  elsif ($mmx_pre == 3) {
    $self->{proc} = $sse2_proc;
    return "movq xmm$mm,xmm$rm" if $mod == 3;
    return "movq xmm$mm," . $self->modrm($mod, $rm, "qword");
  }
  return $self->bad_op();
} # twobyte_7e

sub twobyte_7f {
  my ($self) = @_;
  my ($mod, $mm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $mmx_proc;
    my $dest = $self->modrm($mod, $rm, "qword");
    return "movq $dest,mm$mm";
  }
  $self->{proc} = $sse2_proc;
  my $dest = $self->modrm($mod, $rm, "dqword");
  if    ($mmx_pre == 1) { return "movdqa $dest,xmm$mm" }
  elsif ($mmx_pre == 3) { return "movdqa $dest,xmm$mm" }
  return $self->bad_op();
} # twobyte_7f

sub twobyte_ae {
  my ($self) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  if ($mod == 3) {
    if    ($op == 5) { $self->{proc} = $sse2_proc; return "lfence" }
    elsif ($op == 6) { $self->{proc} = $sse2_proc; return "mfence" }
    elsif ($op == 7) { $self->{proc} = $sse_proc;  return "sfence" }
  }
  elsif ($op == 0) {
    $self->{proc} = 686;
    return "fxsave "  . $self->modrm($mod, $rm, "");
  }
  elsif ($op == 1) {
    $self->{proc} = 686;
    return "fxrstor " . $self->modrm($mod, $rm, "");
  }
  elsif ($op == 2) {
    $self->{proc} = $sse_proc;
    return "ldmxcsr " . $self->modrm($mod, $rm, "dword");
  }
  elsif ($op == 3) {
    $self->{proc} = $sse_proc;
    return "stmxcsr " . $self->modrm($mod, $rm, "dword");
  }
  elsif ($op == 7) {
    $self->{proc} = $sse2_proc;
    return "clflush " . $self->modrm($mod, $rm, "");
  }
  return $self->bad_op();
} # twobyte_ae

sub twobyte_c2 {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  my ($op, $arg);
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    $op = "cmpps";
    $arg = $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    $op = "cmppd";
    $arg = $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    $op = "cmpps";
    $arg = $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 3) {
    $self->{proc} = $sse_proc;
    $op = "cmpss";
    $arg = ($mod == 3) ? $arg = "xmm$rm" : $self->modrm($mod, $rm, "dword");
  }
  else { return $self->bad_op() }
  my $imm = $self->next_byte();
  return sprintf "%s xmm%d,%s,0x%x", $op, $xmm, $arg, $imm;
} # twobyte_c2

sub twobyte_c4 {
  my ($self) = @_;
  my ($mod, $mm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if    ($mmx_pre == 0) { $self->{proc} = $sse_proc;  $mm = "mm$mm"  }
  elsif ($mmx_pre == 1) { $self->{proc} = $sse2_proc; $mm = "xmm$mm" }
  else { return $self->bad_op() }
  my $src = $self->modrm($mod, $rm);
  return sprintf "pinsrw %s,%s,0x%x", $mm, $src, $self->next_byte();
} # twobyte_c4

sub twobyte_c5 {
  my ($self) = @_;
  my ($mod, $reg, $mm) = $self->split_next_byte();
  return $self->bad_op() unless $mod == 3;
  my $mmx_pre = $self->mmx_prefix();
  if    ($mmx_pre == 0) { $self->{proc} = $sse_proc;  $mm = "mm$mm"  }
  elsif ($mmx_pre == 1) { $self->{proc} = $sse2_proc; $mm = "xmm$mm" }
  else { return $self->bad_op() }
  return sprintf "pextrw %s,%s,0x%x", $longregs[$reg], $mm,
      $self->next_byte();
} # twobyte_c5

sub twobyte_c6 {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  my $op;
  if    ($mmx_pre == 0) { $self->{proc} = $sse_proc;  $op = "shufps" }
  elsif ($mmx_pre == 1) { $self->{proc} = $sse2_proc; $op = "shufpd" }
  else { return $self->bad_op() }
  my $src = $self->modrm($mod, $rm, "dqword");
  return sprintf "%s xmm%d,%s,0x%x", $op, $xmm, $src, $self->next_byte();
} # twobyte_c6

sub twobyte_d6 {
  my ($self) = @_;
  $self->{proc} = $sse2_proc;
  my ($mod, $mm, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 1) {
    return "movq xmm$rm,xmm$mm" if $mod == 3;
    my $dest = $self->modrm($mod, $rm, "qword");
    return "movq $dest,xmm$mm"
  }
  elsif ($mmx_pre == 2) { return "movdq2q mm$rm,xmm$mm" }
  elsif ($mmx_pre == 3) { return "movq2dq xmm$rm,mm$mm" }
  return $self->bad_op();
} # twobyte_d6

sub twobyte_d7 {
  my ($self) = @_;
  my ($mod, $reg, $mm) = $self->split_next_byte();
  return $self->bad_op() unless $mod == 3;
  my $mmx_pre = $self->mmx_prefix();
  if    ($mmx_pre == 0) { $self->{proc} = $sse_proc;  $mm = "mm$mm"  }
  elsif ($mmx_pre == 1) { $self->{proc} = $sse2_proc; $mm = "xmm$mm" }
  else { return $self->bad_op() }
  return sprintf "pmovmskb %s,%s", $longregs[$reg], $mm;
} # twobyte_d7

sub twobyte_e6 {
  my ($self) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  $self->{proc} = $sse2_proc;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 1) {
    return "cvtpd2dq xmm$xmm," . $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 2) {
    return "cvtpd2dq xmm$xmm," . $self->modrm($mod, $rm, "dqword");
  }
  elsif ($mmx_pre == 3) {
    return "cvtdq2pd xmm$xmm,xmm$rm" if $mod == 3;
    return "cvtdq2pd xmm$xmm," . $self->modrm($mod, $rm, "qword");
  }
  return $self->bad_op();
} # twobyte_e6

sub twobyte_e7 {
  my ($self) = @_;
  my ($mod, $reg, $rm) = $self->split_next_byte();
  return $self->bad_op() if $mod == 3;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    my $dest = $self->modrm($mod, $rm, "qword");
    return "movntq $dest,mm$reg";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    my $dest = $self->modrm($mod, $rm, "dqword");
    return "movntdq $dest,xmm$reg";
  }
  return $self->bad_op();
} # twobyte_e7

sub twobyte_f7 {
  my ($self) = @_;
  my ($mod, $reg, $rm) = $self->split_next_byte();
  return $self->bad_op() unless $mod == 3;
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "maskmovq mm$reg,mm$rm";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "maskmovdqu xmm$reg,xmm$rm"
  }
  return $self->bad_op();
} # twobyte_f7

sub load_far {
  my ($self, $seg) = @_;
  my ($mod, $reg, $rm) = $self->split_next_byte();
  my $src = $self->modrm($mod, $rm, iflong($self, "far32", "far"));
  return "l$seg $regs{$self->{data_size}}[$reg],$src";
} # load_far

sub seg_op {
  my ($self, $seg, $proc) = @_;
  $self->{seg_reg} = "$seg:";
  my $op = $self->_disasm();
  $self->{seg_reg} = "";
  $self->{proc} = $proc if defined($proc) && $self->{proc} < $proc;
  return $op;
} # seg_op

sub op_reg {
  my ($self, $op, $byte) = @_;
  return "$op $regs{$self->{data_size}}[$byte&7]";
} # op_reg

sub op_r_rm {
  my ($self, $op, $size) = @_;
  $size ||= $self->{data_size};
  my ($mod, $reg, $rm) = $self->split_next_byte();
  my $src = $self->modrm($mod, $rm, $size);
  return "$op $regs{$size}[$reg],$src";
} # op_r_rm

sub op_rm_r {
  my ($self, $op, $size) = @_;
  $size ||= $self->{data_size};
  my ($mod, $reg, $rm) = $self->split_next_byte();
  my $dest = $self->modrm($mod, $rm, $size);
  return "$op $dest,$regs{$size}[$reg]";
} # op_rm_r

sub arith_op {
  my ($self, $op, $byte) = @_;
  $byte &= 7;
  if ($byte == 0) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm, "byte");
    return "$op $dest,$byteregs[$reg]";
  }
  elsif ($byte == 1) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $dest = $self->modrm($mod, $rm);
    return "$op $dest,$regs{$self->{data_size}}[$reg]";
  }
  elsif ($byte == 2) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $src = $self->modrm($mod, $rm, "byte");
    return "$op $byteregs[$reg],$src";
  }
  elsif ($byte == 3) {
    my ($mod, $reg, $rm) = $self->split_next_byte();
    my $src = $self->modrm($mod, $rm);
    return "$op $regs{$self->{data_size}}[$reg],$src";
  }
  elsif ($byte == 4) {
    return sprintf "%s al,0x%x", $op, $self->next_byte();
  }
  elsif ($byte == 5) {
    my $e = iflong($self, "e", "");
    return sprintf "%s %sax,0x%x", $op, $e, $self->get_val();
  }
  die "can't happen";
} # arith_op

sub shift_op {
  my ($self, $dist, $size) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  return $self->bad_op() if $op == 6;
  my $arg = $self->modrm($mod, $rm, $size);
  return "$shift_grp[$op] $arg,$dist";
} # shift_op

sub shift_imm {
  my ($self, $size) = @_;
  $self->{proc} = 186;
  my ($mod, $op, $rm) = $self->split_next_byte();
  return $self->bad_op() if $op == 6;
  my $arg = $self->modrm($mod, $rm, $size);
  return sprintf "%s %s,0x%x", $shift_grp[$op], $arg, $self->next_byte();
} # shift_imm

sub mov_imm {
  my ($self, $size) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  return $self->bad_op() unless $op == 0;
  my $dest = $self->modrm($mod, $rm, $size);
  return sprintf "mov %s,0x%x", $dest, $self->get_val($size);
} # mov_imm

sub unary_op {
  my ($self, $size) = @_;
  my ($mod, $op, $rm) = $self->split_next_byte();
  my $arg = $self->modrm($mod, $rm, $size);
  if ($op == 0) {
    return sprintf "test %s,0x%x", $arg, $self->get_val($size)
  }
  elsif ($op == 1) { return $self->bad_op() }
  else { return "$unary_grp[$op] $arg" }
} # unary_op

sub mmx_op {
  my ($self, $op, $proc) = @_;
  my ($mod, $reg, $rm) = $self->split_next_byte();
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $proc || $mmx_proc;
    my $dest = $self->modrm($mod, $rm, "qword");
    return "$op mm$reg,$dest";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    my $dest = $self->modrm($mod, $rm, "dqword");
    return "$op xmm$reg,$dest";
  }
  return $self->bad_op();
} # mmx_op

sub mmx_shift_imm {
  my ($self, $op, $mm) = @_;
  my $mmx_pre = $self->mmx_prefix();
  if    ($mmx_pre == 0) { $self->{proc} = $mmx_proc;  $mm = "mm$mm"  }
  elsif ($mmx_pre == 1) { $self->{proc} = $sse2_proc; $mm = "xmm$mm" }
  else { return $self->bad_op() }
  return sprintf "%s %s,0x%x", $op, $mm, $self->next_byte();
} # mmx_shift_imm

sub sse_op2 {
  my ($self, $op) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $src = $self->modrm($mod, $rm, "dqword");
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "${op}s xmm$xmm,$src";
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    return "${op}d xmm$xmm,$src";
  }
  return $self->bad_op();
} # sse_op2

sub sse_op4 {
  my ($self, $op) = @_;
  my ($mod, $xmm, $rm) = $self->split_next_byte();
  my $src = $self->modrm($mod, $rm, "dqword");
  my $mmx_pre = $self->mmx_prefix();
  if ($mmx_pre == 0) {
    $self->{proc} = $sse_proc;
    return "${op}ps xmm$xmm,$src";
  }
  elsif ($mmx_pre == 1) {
    $self->{proc} = $sse2_proc;
    return "${op}pd xmm$xmm,$src";
  }
  elsif ($mmx_pre == 2) {
    $self->{proc} = $sse2_proc;
    return "${op}sd xmm$xmm,$src";
  }
  elsif ($mmx_pre == 3) {
    $self->{proc} = $sse_proc;
    return "${op}ss xmm$xmm,$src";
  }
  return $self->bad_op();
} # sse_op4

sub bad_op {
  my ($self) = @_;
  $self->{error} = "bad opcode";
  return undef;
} # bad_op

sub modrm {
  my ($self, $mod, $rm, $data_size) = @_;
  defined($data_size) or $data_size = $self->{data_size};
  if ($mod == 3) {
    my $regset = $regs{$data_size};
    return $regset->[$rm] if $regset;
    $self->{error} = "bad address mode";
    return "!badreg($rm)";
  }

  my $addr_size = $self->{addr_size};
  my $seg = $self->{seg_reg};
  my $addr;
  if ($addr_size eq "dword") {
    if ($rm == 4) {
      my ($scale, $index, $base) = $self->split_next_byte();
      $scale = 1 << $scale;
      if ($mod == 0 && $base == 5) {
        my $off = $self->next_long();
        $addr = sprintf "0x%x", $off;
        if ($index == 4) { }
        elsif ($scale == 1) { $addr = "$longregs[$index]+$addr" }
        else { $addr = "$longregs[$index]*$scale+$addr" }
      }
      elsif ($index == 4) { $addr = $longregs[$base] }
      elsif ($scale == 1) { $addr = "$longregs[$index]+$longregs[$base]" }
      else { $addr = "$longregs[$index]*$scale+$longregs[$base]" }
    }
    elsif ($mod == 0 && $rm == 5) {
      $addr = sprintf "0x%x", $self->next_long();
    }
    else { $addr = $longregs[$rm] }

    if ($mod == 1) {
      my $off = $self->next_byte();
      $off |= 0xffffff00 if $off & 0x80;
      $addr = sprintf "%s+0x%x", $addr, $off;
    }
    elsif ($mod == 2) {
      $addr = sprintf "%s+0x%x", $addr, $self->next_long();
    }
  }
  elsif ($addr_size eq "word") {
    if ($mod == 0 && $rm == 6) {
      $addr = sprintf "0x%x", $self->next_word();
    }
    else {
      $addr = $index16[$rm];
      $seg ||= "ss:" if $rm == 2 || $rm == 3 || $rm == 6;
    }

    if ($mod == 1) {
      my $off = $self->next_byte();
      $off |= 0xff00 if $off & 0x80;
      $addr = sprintf "%s+0x%x", $addr, $off;
    }
    elsif ($mod == 2) {
      $addr = sprintf "%s+0x%x", $addr, $self->next_word();
    }
  }
  else { die "can't happen" }

  return "$data_size\[$seg$addr]";
} # modrm

sub next_byte {
  my ($self) = @_;
  my $pos = $self->{pos};
  $self->{pos} = $pos + 1;
  return 0 if $pos >= $self->{lim};
  my $byte = $self->{text}->get_byte($pos);
  if (!defined $byte) { $self->{error} = "end of data"; return 0; }
  return $byte;
} # next_byte

sub split_next_byte {
  my ($self) = @_;
  my $pos = $self->{pos};
  $self->{pos} = $pos + 1;
  return (0,0,0) if $pos >= $self->{lim};
  my $byte = $self->{text}->get_byte($pos);
  if (!defined $byte) { $self->{error} = "end of data"; return (0,0,0); }
  return ( ($byte >> 6) & 3, ($byte >> 3) & 7, $byte & 7 );
} # split_next_byte

sub next_word {
  my ($self) = @_;
  my $pos = $self->{pos};
  my $newpos = $self->{pos} = $pos + 2;
  return 0 if $newpos > $self->{lim};
  my $word = $self->{text}->get_word($pos);
  if (!defined $word) { $self->{error} = "end of data"; return 0; }
  return $word;
} # next_word

sub next_long {
  my ($self) = @_;
  my $pos = $self->{pos};
  my $newpos = $self->{pos} = $pos + 4;
  return 0 if $newpos > $self->{lim};
  my $long = $self->{text}->get_long($pos);
  if (!defined $long) { $self->{error} = "end of data"; return 0; }
  return $long;
} # next_long

sub get_byteval {
  my ($self) = @_;
  my $b = $self->next_byte();
  return $b unless $b & 0x80;
  my $size = $self->{data_size};
  return $b | 0xffffff00 if $size eq "dword";
  return $b |     0xff00 if $size eq "word";
  return $b;
} # get_byteval

sub get_val {
  my ($self, $size) = @_;
  $size ||= $self->{data_size};
  return $self->next_long() if $size eq "dword";
  return $self->next_word() if $size eq "word";
  return $self->next_byte() if $size eq "byte";
  die "can't happen";
} # get_val

sub abs_addr {
  my ($self, $data_size) = @_;
  $data_size ||= $self->{data_size};
  my $addr_size = $self->{addr_size};
  my $addr;
  if    ($addr_size eq "dword") { $addr = $self->next_long() }
  elsif ($addr_size eq "word")  { $addr = $self->next_word() }
  else { die "can't happen" }
  return sprintf "%s[%s0x%x]", $data_size, $self->{seg_reg}, $addr;
} # abs_addr

sub string_esi {
  my ($self, $size) = @_;
  return sprintf "%s[%s%ssi]", $size || $self->{data_size},
      $self->{seg_reg}, $self->{addr_size} eq "dword" ? "e" : "";
} # string_esi

sub string_edi {
  my ($self, $size) = @_;
  # no segment override with es:edi
  return sprintf "%s[es:%sdi]", $size || $self->{data_size},
      $self->{addr_size} eq "dword" ? "e" : "";
} # string_edi

sub eip_byteoff {
  my ($self) = @_;
  my $off = $self->next_byte();
  $off |= 0xffffff00 if $off & 0x80;
  $off += $self->{pos};
  my $size = $self->{addr_size};
  return $off & 0xffffffff if $size eq "dword";
  return $off &     0xffff if $size eq "word";
  die "can't happen";
} # eip_byteoff

sub eip_off {
  my ($self) = @_;
  my $size = $self->{data_size};
  if ($size eq "dword") {
    my $off = $self->next_long();
    return ($off + $self->{pos}) & 0xffffffff;
  }
  elsif ($size eq "word") {
    my $off = $self->next_word();
    return ($off + $self->{pos}) & 0xffff;
  }
  die "can't happen";
} # eip_off

sub iflong {
  my ($disasm, $if, $else) = @_;
  return $disasm->{data_size} eq "dword" ? $if : $else;
} # iflong

sub toggle_size {
  my ($size) = @_;
  return "word"  if $size eq "dword";
  return "dword" if $size eq "word";
  die "can't happen";
} # toggle_size

sub mmx_prefix {
  my ($self) = @_;
  my $prefix = $self->{mmx_pre};
  $self->{mmx_pre} = 0;
  return $prefix;
} # mmx_prefix

1 # end X86.pm
__END__

=head1 NAME

Disassemble::X86 - Disassemble Intel x86 binary code

=head1 SYNOPSIS

  use Disassemble::X86;
  $d = Disassemble::X86->new(text => $text_seg);
  while (defined( $op = $d->disasm() )) {
    printf "%04x  %s\n", $d->op_start(), $op;
  }

=head1 DESCRIPTION

This module disassembles binary-coded Intel x86 machine instructions
into a human- and machine-readable format.

=head1 OUTPUT

Output is in Intel assembler syntax, with a few minor
exceptions. Certain conventions are used in order to make it easier
for programs to process the output of the disassembler. All output is
in lower case. If opcode prefixes are present (other than segment
register overrides and address/operand size overrides), they precede
the opcode mnemonic separated by single space characters. If the
instruction has any operands, they appear after another space,
separated by commas.

There is no whitespace between or within operands, so you can
separate the parts of an instruction with C<split ' '>. In order
to make this possible, the word "PTR" is omitted from memory
operands.

  mov 0x42, WORD PTR [edx]    becomes    mov 0x42,word[edx]

The memory operand size (byte, word, etc.) is usually included in the
operand, even if it can be determined from context. That way, the
size is not lost if later processing separates the operand from the
rest of the instruction. (Some memory operands have no real
"size", though.)

  ADD eax,[0x1234]    becomes    add eax,dword[0x1234]

Unlike AT&T assembler syntax, individual operands never contain
embedded commas. This means that you can safely break up the operand
list with C<split/,/>.

  lea 0x0(,%ebx,4),%edi    becomes    lea edi,[ebx*4+0x0]

=head1 METHODS

=head2 new
 
  $d = Disassemble::X86->new(
      text      => $text_seg,
      start     => $text_load_addr,
      pos       => $initial_eip,
      addr_size => 32,
      data_size => 32,
      size      => 32,
  );

Creates a new disassembler object. There are a number of named
parameters which can be given, all of which are optional.

=over 6

=item text

The so-called text segment, which consists of the binary data
to be disassembled. It can be given either as a string or as a
C<Disassemble::X86::MemRegion> object.

=item start

The address at which the text segment would be loaded to execute
the program. This parameter is ignored if C<text> is a MemRegion
object, and defaults to 0 otherwise.

=item pos

The address at which disassembly is to begin, unless changed by
C<< $d->pos() >>. Default value is the start of the text segment.

=item addr_size

Gives the address size (16 or 32 bit) which will be used when
disassembling the code. Default is 32 bits. See below.

=item data_size

Gives the data operand size, similar to C<addr_size>.

=item size

Sets both C<addr_size> and C<data_size>.

=back

=head2 disasm

  $op = $d->disasm();

Disassembles a single machine instruction from the current position.
Advances the current position to the next instruction. If no valid
instruction is found at the current position, returns C<undef>
and leaves the current position unchanged. In that case, you can check
C<< $d->error() >> for more information.

=head2 addr_size

  $d->addr_size(16);

Sets the address size for disassembled code. Valid values are
16, "word", 32, "dword", and "long", but some of these are
synonyms. With no argument, returns the current address size as
"word" or "dword".

=head2 data_size

  $d->data_size("long");

Similar to addr_size above, but sets the data operand size.

=head2 pos

  $d->pos($new_pos);

Sets the current disassembly position. With no argument, returns the
current position.

=head2 text

  $text = $d->text();

Returns the text segment as a C<Disassemble::X86::MemRegion> object.

=head2 at_end

  until ( $d->at_end() ) {
    ...
  }

Returns true if the current disassembly position has reached the
end of the text segment.

=head2 contains

  if ( $d->contains($addr) ) {
    ...
  }

Returns true if C<$addr> is within the memory region being disassembled.

=head2 next_byte

  $byte = $d->next_byte();

Returns the next byte from the current disassembly position as an
integer value, and advances the current position by one. This can
be used to skip over invalid instructions that are encountered
during disassembly. If the current position is not valid, returns 0,
but still advances the current position. Attempting to read beyond
the 15-byte opcode size limit will cause an error.

=head2 op

This and the following functions return information about the previously
disassembled machine instruction. C<< $d->op() >> returns the instruction
itself, which is the same as the value returned by C<disasm>.

=head2 op_start 

Returns the starting address of the instruction.

=head2 op_len   

Returns the length of the instruction, in bytes.

=head2 op_proc

Returns the minimum processor model required. For instructions present
in the original 8086 processor, the value 86 is returned. For 
instructions supported by the 8087 math coprocessor, the value is
87. Instructions initially introduced with the Pentium return 586,
and so on. Note that setting the address or operand size to 32 bits
requires at least a 386. Other possible return values are "mmx",
"sse", "sse2", "3dnow", and "3dnow-e" (for extended 3DNow! instructions).

This information should be used carefully, because there may be subtle
differences between different steppings of the same processor. In some
cases, you must check the CPUID instruction to see exactly what your
processor supports. When in doubt, consult the
I<Intel Architecture Software Developer's Manual>.

=head2 op_error

Returns the error message encountered while trying to disassemble
an instruction.

=head1 LIMITATIONS

Multiple discontinuous text segments are not supported. Use additional
C<Disassemble::X86> objects if you need them.

Some of the more exotic instructions like cache control and MMX
extensions have not been thoroughly tested. Please let me know if
you find something that is broken.

=head1 SEE ALSO

L<Disassemble::X86::MemRegion>

=head1 AUTHOR

Bob Mathews E<lt>bobmathews@alumni.calpoly.eduE<gt>

=head1 COPYRIGHT

Copyright (c) 2002 Bob Mathews. All rights reserved.

This program is free software; you can redistribute it and/or
modify it under the same terms as Perl itself.

=cut

