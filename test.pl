# Before `make install' is performed this script should be runnable with
# `make test'. After `make install' it should work as `perl test.pl'

#########################

use Test;
use Test::More "no_plan";
use Disassemble::X86;
ok(1, "Load module");

#########################

my @text = (
  # simple ops
  [0, 0, "aaa",     qw(37)],
  [0, 0, "aad 0xa", qw(d5 0a)],
  [0, 0, "aam 0xa", qw(d4 0a)],
  [0, 0, "aas",     qw(3f)],
  [0, 0, "clc",     qw(f8)],
  [0, 0, "cld",     qw(fc)],
  [0, 0, "cli",     qw(fa)],
  [0, 0, "clts",    qw(0f 06)],
  [0, 0, "cmc",     qw(f5)],
  [0, 0, "cpuid",   qw(0f a2)],
  [0, 0, "daa",     qw(27)],
  [0, 0, "das",     qw(2f)],
  [0, 0, "emms",    qw(0f 77)],
  [0, 0, "hlt",     qw(f4)],
  [0, 0, "int 0x3", qw(cc)],
  [0, 0, "int 0xe", qw(cd 0e)],
  [0, 0, "into",    qw(ce)],
  [0, 0, "invd",    qw(0f 08)],
  [0, 0, "lahf",    qw(9f)],
  [0, 0, "leave",   qw(c9)],

  # simple floating-point ops
  [0, 0, "f2xm1",   qw(d9 f0)],
  [0, 0, "fabs",    qw(d9 e1)],
  [0, 0, "fchs",    qw(d9 e0)],
  [0, 0, "fnclex",  qw(db e2)],
  [0, 0, "fcos",    qw(d9 ff)],
  [0, 0, "fdecstp", qw(d9 f6)],
  [0, 0, "fincstp", qw(d9 f7)],
  [0, 0, "fninit",  qw(db e3)],
  [0, 0, "fld1",    qw(d9 e8)],
  [0, 0, "fldl2t",  qw(d9 e9)],
  [0, 0, "fldl2e",  qw(d9 ea)],
  [0, 0, "fldpi",   qw(d9 eb)],
  [0, 0, "fldlg2",  qw(d9 ec)],
  [0, 0, "fldln2",  qw(d9 ed)],
  [0, 0, "fldz",    qw(d9 ee)],
  [0, 0, "fnop",    qw(d9 d0)],
  [0, 0, "fpatan",  qw(d9 f3)],
  [0, 0, "fprem",   qw(d9 f8)],
  [0, 0, "fprem1",  qw(d9 f5)],
  [0, 0, "fptan",   qw(d9 f2)],
  [0, 0, "frndint", qw(d9 fc)],
  [0, 0, "fscale",  qw(d9 fd)],
  [0, 0, "fsin",    qw(d9 fe)],
  [0, 0, "fsincos", qw(d9 fb)],
  [0, 0, "fsqrt",   qw(d9 fa)],
  [0, 0, "ftst",    qw(d9 e4)],
  [0, 0, "fxam",    qw(d9 e5)],
  [0, 0, "fxtract", qw(d9 f4)],
  [0, 0, "fyl2x",   qw(d9 f1)],
  [0, 0, "fyl2xp1", qw(d9 f9)],

  # semi-simple ops
  [0, 16, "cbw",   qw(98)],
  [0, 32, "cwde",  qw(98)],
  [0, 16, "cwd",   qw(99)],
  [0, 32, "cdq",   qw(99)],
  [0, 16, "iret",  qw(cf)],
  [0, 32, "iretd", qw(cf)],

  # move
  [16, 0,  "mov cl,dh",                   qw(88 f1)],
  [16, 16, "mov word[bx+di+0x49],di",     qw(89 79 49)],
  [32, 0,  "mov dh,byte[eax+0xfe67bdb2]", qw(8a b0 b2 bd 67 fe)],
  [32, 32, "mov ebp,dword[ebp+0x17]",     qw(8b 6d 17)],
  [16, 0,  "mov word[si+0x2123],ss",      qw(8c 94 23 21)],
  [32, 0,  "mov es,si",                   qw(8e c6)],
  [32, 0,  "mov al,byte[0x58166c84]",     qw(a0 84 6c 16 58)],
  [32, 16, "mov ax,word[0xc179f846]",     qw(a1 46 f8 79 c1)],
  [16, 0,  "mov byte[fs:0x2582],al",      qw(64 a2 82 25)],
  [16, 32, "mov dword[gs:0xae54],eax",    qw(65 a3 54 ae)],
  [0,  0,  "mov ch,0x96",                 qw(b5 96)],
  [0,  16, "mov cx,0xc9c9",               qw(b9 c9 c9)],
  [0,  32, "mov esp,0xdeaeb46",           qw(bc 46 eb ea 0d)],
  [32, 0,  "mov byte[edi+0x55],0x6e",     qw(c6 47 55 6e)],
  [32, 32, "mov dword[edi],0xa50ad4b1",   qw(c7 07 b1 d4 0a a5)],

  # arithmetic ops
  [0,  0,  "add al,0x98",                 qw(04 98)],
  [0,  16, "adc ax,0x55a9",               qw(15 a9 55)],
  [0,  32, "and eax,0xc7c38598",          qw(25 98 85 c3 c7)],
  [16, 0,  "cmp byte[ss:bp+di],ch",       qw(38 2b)],
  [16, 16, "mov word[bx+di+0x30],sp",     qw(89 61 30)],
  [16, 32, "or dword[si+0x11],ebp",       qw(09 6c 11)],
  [32, 0,  "sbb al,ch",                   qw(1a c5)],
  [32, 16, "sub bp,word[ebp+0xe55ac0ea]", qw(2b ad ea c0 5a e5)],
  [32, 32, "xor esi,dword[edx+ecx+0xa]",  qw(33 74 11 0a)],
  [16, 0,  "and byte[bx+si+0x8eda],0xdf", qw(80 a0 da 8e df)],
  [16, 16, "xor di,0x9289",               qw(81 f7 89 92)],
  [32, 32, "or dword[eax],0x1867327f",    qw(81 08 7f 32 67 18)],
  [32, 16, "sub word[esi*8+0x10234482],0xffd9", qw(83 2c f5 82 44 23 10 d9)],
  [16, 32, "cmp edx,0x1f",                qw(83 fa 1f)],
  [16, 0,  "idiv byte[di+0x2853]",        qw(f6 bd 53 28)],
  [16, 16, "div word[si]",                qw(f7 34)],
  [32, 32, "mul ecx",                     qw(f7 e1)],
  [16, 16, "imul di,word[ss:bp+si+0xffa8]",        qw(0f af 7a a8)],
  [32, 32, "imul esi,dword[ecx+0x6129b97f]",       qw(0f af b1 7f b9 29 61)],
  [32, 16, "imul sp,word[ebx],0xffc1",             qw(6b 23 c1)],
  [16, 32, "imul esi,dword[ss:bp+di+0xa1ec],0x1b", qw(6b b3 ec a1 1b)],
  [16, 16, "imul di,bp,0x2555",                    qw(69 fd 55 25)],
  [32, 32, "imul edx,dword[edx],0x5db0438a",       qw(69 12 8a 43 b0 5d)],

  # unary ops
  [16, 0,  "dec byte[ss:bp+di+0x5f0a]",   qw(fe 8b 0a 5f)],
  [16, 16, "dec word[bx]",                qw(ff 0f)],
  [32, 32, "dec dword[0x2e070857]",       qw(ff 0d 57 08 07 2e)],
  [0,  16, "dec sp",                      qw(4c)],
  [0,  32, "dec ebp",                     qw(4d)],
  [32, 0,  "inc cl",                      qw(fe c1)],
  [32, 16, "inc word[edi+0xffffffb1]",    qw(ff 47 b1)],
  [16, 32, "inc ebx",                     qw(ff c3)],
  [0,  16, "inc cx",                      qw(41)],
  [0,  32, "inc ebx",                     qw(43)],

  # bit bashing
  [16, 16, "bsr cx,word[bx]",              qw(0f bd 0f)],
  [32, 32, "bsf ecx,dword[edx+0xffffff83]", qw(0f bc 4a 83)],
  [0,  0,  "bswap esp",                    qw(0f cc)],
  [32, 16, "bt word[edx],dx",              qw(0f a3 12)],
  [16, 32, "bts edi,esi",                  qw(0f ab f7)],
  [16, 16, "btc word[ss:bp+0x75],0x9f",    qw(0f ba 7e 75 9f)],
  [32, 32, "btr dword[ebp+0xa0ca131d],0x7", qw(0f ba b5 1d 13 ca a0 07)],

  # string ops
  [16, 0,  "cmps byte[es:si],byte[es:di]", qw(26 a6)],
  [16, 16, "cmps word[ss:si],word[es:di]", qw(36 a7)],
  [32, 32, "cmps dword[esi],dword[es:edi]", qw(a7)],
  [32, 0,  "ins byte[es:edi],byte[dx]",    qw(6c)],
  [32, 16, "ins word[es:edi],word[dx]",    qw(6d)],
  [16, 32, "ins dword[es:di],dword[dx]",   qw(6d)],
  [16, 0,  "lods al,byte[si]",             qw(ac)],
  [16, 16, "lods ax,word[si]",             qw(ad)],
  [32, 32, "lods eax,dword[esi]",          qw(ad)],

  # address ops
  [16, 16, "lds dx,far[0x5b6a]",           qw(c5 16 6a 5b)],
  [32, 32, "lss ebx,far32[ebp+0x484b56bc]", qw(0f b2 9d bc 56 4b 48)],
  [32, 16, "les dx,far[edi]",              qw(c4 17)],
  [32, 32, "lfs eax,far32[0x287aaceb]",    qw(0f b4 05 eb ac 7a 28)],
  [16, 32, "lgs eax,far32[ss:bp+0x88ea]",  qw(0f b5 86 ea 88)],
  [16, 16, "lea di,[bx+di]",               qw(8d 39)],
  [32, 32, "lea esi,[edi+0xffffffaa]",     qw(8d 77 aa)],

  # control transfer
  [16, 16, "call word[ss:bp+di+0x435]",    qw(ff 93 35 04)],
  [32, 32, "call dword[0x86395426]",       qw(ff 15 26 54 39 86)],
  [0,  16, "call 0x851a:0x1a36",           qw(9a 36 1a 1a 85)],
  [0,  32, "call 0xf9ff:0xb9b3f74a",       qw(9a 4a f7 b3 b9 ff f9)],
  [32, 16, "call far[cs:edx]",             qw(2e ff 1a)],
  [16, 32, "call far32[si+0xffaa]",        qw(ff 5c aa)],

  # i/o ops
  [0,  0,  "in al,byte[0x1b]",             qw(e4 1b)],
  [0,  16, "in ax,word[0x8c]",             qw(e5 8c)],
  [0,  0,  "in al,byte[dx]",               qw(ec)],
  [0,  32, "in eax,dword[dx]",             qw(ed)],

  # access control
  [16, 16, "lar bx,word[ss:bp+di+0x18]",   qw(0f 02 5b 18)],
  [32, 32, "lar eax,dword[eax+edx+0xfffffff8]", qw(0f 02 44 02 f8)],
  [16, 0,  "lgdt [ss:bp+di]",              qw(0f 01 13)],
  [32, 0,  "lidt [edx]",                   qw(0f 01 1a)],
  [32, 0,  "lldt word[eax]",               qw(0f 00 10)],
  [16, 0,  "lmsw word[bx+si+0xffb7]",      qw(0f 01 70 b7)],
  [32, 16, "lsl bp,word[edx+0xdf6af51e]",  qw(0f 03 aa 1e f5 6a df)],
  [16, 32, "lsl eax,dword[bx+di+0xdc23]",  qw(0f 03 81 23 dc)],

  # misc
  [16, 0,  "arpl word[ss:bp+di+0x36],bx",  qw(63 5b 36)],
  [32, 32, "bound edi,[0xc6cd9909]",       qw(62 3d 09 99 cd c6)],
  [16, 16, "bound si,[ss:bp+0x5d18]",      qw(62 b6 18 5d)],
  [32, 0,  "clflush [ebp*8+esi+0x1e415eed]", qw(0f ae bc ee ed 5e 41 1e)],
  [32, 32, "cmove edx,dword[esi]",         qw(0f 44 16)],
  [16, 16, "cmovpo cx,word[0xafb2]",       qw(0f 4b 0e b2 af)],
  [16, 0,  "cmpxchg dl,bh",                qw(0f b0 fa)],
  [32, 32, "cmpxchg dword[ecx+0xffffffa2],esp", qw(0f b1 61 a2)],
  [32, 0,  "cmpxchg8b qword[ebp+0xae9c8628]", qw(0f c7 8d 28 86 9c ae)],
  [0,  0,  "enter 0xba7e,0x57",            qw(c8 7e ba 57)],
  [16, 0,  "invlpg [ds:bp+di]",            qw(3e 0f 01 3b)],
  [32, 0,  "ldmxcsr dword[ebp+0x3dfdb73e]", qw(0f ae 95 3e b7 fd 3d)],
  [0,  0,  "lfence",                       qw(0f ae eb)],
  [16, 16, "lock cmpxchg word[di+0xef9a],sp", qw(f0 0f b1 a5 9a ef)],
  [32, 0,  "ltr word[ebp*2+ecx+0xffffffc2]", qw(0f 00 5c 69 c2)],
);

foreach my $size (16, 32) {
  my $text = "";
  foreach my $instr (@text) {
    $text .= "\x67" if $instr->[0] && $instr->[0] != $size;
    $text .= "\x66" if $instr->[1] && $instr->[1] != $size;
    $text .= join "", map chr hex, @$instr[3 .. $#$instr];
  }
  my $d = Disassemble::X86->new(text => $text, size => $size);
  ok($d, "Create object $size-bit");
  foreach (0 .. $#text) {
    is($d->disasm(), $text[$_][2], "$size-bit instr $_");
  }
  is($d->disasm(), undef, "End of text");
}

# end test.pl
