role BitReader {
    has int64 $!remaining-bits;
    has int64 $!remaining-bit-count;

    method read-bits(int64 $count-in) {
        my int64 $count = $count-in;
        my int64 $ret = 0;
        my int64 $got-bits = 0;
        my @tell = self.tell-bits;

        while $count {
            if (my int64 $rcnt = $!remaining-bit-count min $count) {
                #say "must get $rcnt bits from remaining bits $!remaining-bits.fmt("%b") with mask {(2**$rcnt-1).fmt("%b")}";
                my int64 $new-bits = $!remaining-bits +& (2**$rcnt-1);
                #say "new bits was $new-bits.fmt("%b")";
                $new-bits +<= $got-bits;
                $ret +|= $new-bits;
                $got-bits += $rcnt;
                $!remaining-bits +>= $rcnt;
                $!remaining-bit-count -= $rcnt;
                #say "after, remaining-bits are now $!remaining-bits.fmt("%b") and count $!remaining-bit-count";
                $count -= $rcnt;
            }
            if $count {
                #say "read 1 byte";
                $!remaining-bits = self.read(1)[0];
                #say "read, remaining-bits now $!remaining-bits.fmt("%08b")";
                $!remaining-bit-count = 8;
            }
        }
        #say "at {@tell} read $count-in gave " ~ $ret.fmt('%0' ~ $count-in ~ 'b');
        $ret;
    }

    method tell-bits() {
        my $pos = self.tell;
        my $rem = (8-$!remaining-bit-count);
        if $rem == 8 { $pos++; $rem = 0; }
        ($pos,$rem);
    }
}

sub MAIN($filename) {
    my $fh = $filename.IO.open(:bin) but BitReader or die;

    my $sig = $fh.read-bits(16);
    if $sig == 0x8b1f {

        my $method = $fh.read-bits(8);
        die "unknown method $method" unless $method == 8;
        my $flags = $fh.read-bits(8);
        my $mtime = $fh.read-bits(32);
        my $extra = $fh.read-bits(8);
        my $os = $fh.read-bits(8);
        #say "method $method flags $flags mtime $mtime extra $extra os $os";
        if $flags +& 0x04 {
            my $xlen = $fh.read-bits(16);
            #say "read $xlen extra bytes";
            $fh.read($xlen);
        }
        if $flags +& 0x08 {
            while $fh.read-bits(8) {}
        }
        if $flags +& 0x10 {
            while $fh.read-bits(8) {}
        }
        if $flags +& 0x02 {
            $fh.read-bits(16);
        }
        my $file = inflate($fh);
        say $file.decode('UTF-8');

    } elsif ($sig == 0x4b50) {

        my @files = read-dir($fh);

        #for @files -> $f {
        #    say (
        #        $f<compression-method>,
        #        $f<compressed-size>.fmt("%8.8s"),
        #        $f<uncompressed-size>.fmt("%8.8s"),
        #        $f<file-name>).join(' ');
        #}

        my $file1 = get-file($fh, @files[0]);

        say $file1.decode('UTF-8');
    } else {
        die "Unknown file signature $sig.fmt("%x")";
    }
}

class HuffmanTree {
    has %.tree;
    has @.bits;

    method new-from-bitlengths(@l) {
        my $sym = 0;
        my $bits = -1;
        my @bits;
        my %tree;
        for @l.pairs.grep(*.value).sort({sprintf("%08d%08d",$_.value,$_.key)}) -> $l {
            if $bits != $l.value {
                $sym +<= ($l.value - $bits);
                $bits = $l.value;
                @bits.push($bits);
            }
            #say "populate: "~$sym.fmt("%0"~$bits~"b")~" {$l.key}";
            %tree{$sym.fmt('%0'~$bits~'b')} = $l.key;
            $sym++;
        }
        self.bless(:%tree,:@bits);
    }

    method read-next-symbol($fh) {
        my $read = '';
        my $read-bits = 0;
        for @!bits -> $bits {
            $read ~= $fh.read-bits($bits - $read-bits).fmt('%0'~($bits - $read-bits)~'b').flip;
            $read-bits = $bits;
            #say "trying $bits, read $read";
            if %!tree{$read}:exists {
                return %!tree{$read};
            }
        }
        die "can't find symbol in stream, aborting after $read";
    }
}

sub get-file($fh, $cdir) {
    #say "data of file {$cdir<file-name>}:";

    my $fhdr = read-file-hdr($fh, $cdir<file-header-offset>);
    #say $fhdr.perl;

    my $file-data;
    if $fhdr<compression-method> == 0 {
        $file-data = $fh.read($fhdr<compressed-size>);
    } elsif $fhdr<compression-method> == 8 {
        my $file-data = inflate($fh, $fhdr<compressed-size>, $fhdr<uncompressed-size>);
    } else {
        die "Unsupported compression method $fhdr<compression-method>";
    }
    return $file-data;
}

my int @len-base = (|(0 xx 257),3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258);
my int @dist-base = (1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577);
my int @codelen-order = (16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15);

sub inflate {
    my ($fh, $compressed-size, $uncompressed-size) = @_;

    my $output = Buf.new;

    loop {
        my $flags = $fh.read-bits(3);
        my $is-final = $flags +& 1;
        my $block-type = $flags +& 0b110 +> 1;
        #say "block type $block-type is-final $is-final";

        given $block-type {
            when 0 { # no compression
                # call read-bits to skip the next 5 bits
                $fh.read-bits(5);
                my ($len,$nlen) = read-types($fh,int16,int16);
                # FIXME check len = !nlen
                #say "uncompressed block, len $len nlen $nlen";
                $output.append($fh.read($len).list);
            }
            when 3 {
                die "Illegal block type in compressed data stream";
            }
            default { # huffman
                #say "huffman block";
                my $lit-tree;
                my $dist-tree;
                if $block-type == 1 { # Static huffman
                    die "not implemented";
                } elsif $block-type == 2 { # Dynamic Huffman
                    my $literals = $fh.read-bits(5) + 257;
                    my $distances = $fh.read-bits(5) + 1;
                    my $codelen-size = $fh.read-bits(4) + 4;
                    #say "literals $literals distances $distances codelen-size $codelen-size";

                    # Read the code length huffman tree
                    my @l;
                    for 0..^$codelen-size {
                        @l[@codelen-order[$_]] = $fh.read-bits(3);
                    }
                    my $codelen-tree = HuffmanTree.new-from-bitlengths(@l);

                    # Read a huffman tree with data stored as bits in the code length huffman tree
                    sub read-tree($cl-tree,$count) {
                        my @data;
                        my ($times,$what);
                        my $n = 0;

                        while $n < $count {
                            my $sym = $cl-tree.read-next-symbol($fh);
                            #say "next symbol $sym";
                            given $sym {
                                #say "sym $sym";
                                when 0 <= $_ <= 15 { # literal
                                    $times = 1;
                                    $what = $sym;
                                }
                                when 16 { # repeat last symbol 2-6 times
                                    $times = 3 + $fh.read-bits(2);
                                    $what = @data ?? @data[*-1] !! die "sym 16 encountered without previous data";
                                }
                                when 17 { # repeat 3-11 zeroes
                                    $times = 3 + $fh.read-bits(3);
                                    $what = 0;
                                }
                                when 18 { # repeat 11-139 zeroes
                                    $times = 11 + $fh.read-bits(7);
                                    $what = 0;
                                }
                            }
                            #say "$sym added $what $times times";
                            @data.append($what xx $times);
                            $n += $times;
                        }
                        @data;
                    }

                    #say "read literal table of $literals entries";
                    my @lit = read-tree($codelen-tree, $literals);
                    $lit-tree = HuffmanTree.new-from-bitlengths(@lit);

                    #say "read distance table of $distances entries";
                    my @dist = read-tree($codelen-tree, $distances);
                    $dist-tree = HuffmanTree.new-from-bitlengths(@dist);
                }

                # Now read actual data stored as literal-tree symbols
                # or distance-tree symbols and lengths, which encodes
                # offsets to previously encoded data
                my $data = Buf.new;
                sub x-dist-bits($n) { $n >= 2 ?? ($n +> 1) - 1 !! $n }
                sub x-len-bits($n) { 257 <= $n <= 260 || $n == 285 ?? 0 !! (($n-257) +> 2) - 1 }
                loop {
                    my $r = $lit-tree.read-next-symbol($fh);
                    if 0 <= $r <= 255 {
                        #say "read literal byte $r {chr($r).perl}";
                        $data.append($r);
                    } elsif $r == 256 {
                        #say "data end";
                        last;
                    } elsif 257 <= $r <= 285 {
                        my $len = @len-base[$r] + $fh.read-bits(x-len-bits($r));
                        #say "len $len x {x-len-bits($r)}";
                        my $dist-sym = $dist-tree.read-next-symbol($fh);
                        die "illegal dist symbol $dist-sym" unless 0 <= $dist-sym <= 29;
                        my $dist = @dist-base[$dist-sym] + $fh.read-bits(x-dist-bits($dist-sym));
                        my $end = $data.elems;
                        my $get-cnt = $len;
                        while $get-cnt > $dist {
                            $data.append($data.subbuf($data.elems - $dist));
                            $get-cnt -= $dist;
                        }
                        if $get-cnt == $dist {
                            $data.append($data.subbuf($data.elems - $dist));
                        } else {
                            #say "append {Buf.new($data[* - $dist .. * - $dist + $get-cnt - 1]).decode('UTF-8').perl}";
                            $data.append($data.subbuf($data.elems - $dist, $get-cnt));
                        }
                        #say "dict lookup sym $r, len $len, dist-sym $dist-sym dist $dist got {Buf.new($data[*-$len..*]).decode('UTF-8').perl}";
                    } else {
                        die "Illegal unused literal/length symbol $r";
                    }
                }
                $output.append($data.list);
            }
        }

        last if $is-final;
    }
    $output;
}

sub read-file-hdr($fh, $offset) {
    $fh.seek($offset, SeekFromBeginning);

    my ($signature) = read-types($fh, int32);

    die "Wrong signature $signature.fmt("0x%08x") for central directory at offset $fh.tell" unless $signature == 0x4034b50;

    my %fhdr = <
        version-needed
        bits
        compression-method
        modification-time
        modification-date
        crc32
        compressed-size
        uncompressed-size
        file-name-length
        extra-fields-length
    > «=>» read-types($fh, int16 xx 5, int32 xx 3, int16 xx 2);

    %fhdr<signature> = $signature;

    if %fhdr<file-name-length> {
        %fhdr<file-name> = $fh.read(%fhdr<file-name-length>).decode('UTF-8');
    }

    if %fhdr<extra-fields-length> {
        %fhdr<extra-fields> = $fh.read(%fhdr<extra-fields-length>);
    }

    return %fhdr;
}

sub read-dir($fh) {
    my $ecd = read-ecd($fh);

    $fh.seek($ecd<cdir-offset>, SeekFromBeginning);

    my @files;

    for 1..$ecd<cdir-on-this-disk> -> $i {
        my $cdir = read-cdir($fh);
        push @files, $cdir;
   }

   return @files;
}

sub read-cdir($fh) {
    my ($signature) = read-types($fh, int32);

    die "Wrong signature $signature.fmt("0x%08x") for central directory at offset $fh.tell" unless $signature == 0x2014b50;

    my %cdir = <
        version-made-by
        version-needed
        bits
        compression-method
        modification-time
        modification-date
        crc32
        compressed-size
        uncompressed-size
        file-name-length
        extra-fields-length
        file-comment-length
        disk-num
        internal-attrs
        external-attrs
        file-header-offset
    > «=>» read-types($fh, int16 xx 6, int32 xx 3, int16 xx 5, int32 xx 2);

    %cdir<signature> = $signature;

    if %cdir<file-name-length> {
        %cdir<file-name> = $fh.read(%cdir<file-name-length>).decode('UTF-8');
    }

    if %cdir<extra-fields-length> {
        %cdir<extra-fields> = $fh.read(%cdir<extra-fields-length>);
    }

    if %cdir<file-comment-length> {
        %cdir<file-comment> = $fh.read(%cdir<file-comment-length>).decode('UTF-8');
    }

    return %cdir;
}

sub read-ecd($fh) {
    # offset from end of file
    my $offset = 0;
    my $found_offset;

    loop {
        $offset -= 512;
        # seek to end-$offset, 4 extra bytes in order to have overlap on block boundaries
        $fh.seek($offset-4, SeekFromEnd);
        CATCH { last };

        # read a buffer
        my $buf = $fh.read(516);

        # find 0x06054b50
        loop (my $i=512; $i>0; $i--) {
            if ($buf[$i] == 0x50 && $buf[$i+1] == 0x4b && $buf[$i+2] == 0x05 && $buf[$i+3] == 0x06) {
                $found_offset = $offset + $i - 4;
                last;
            }
        }
        last if $found_offset;
    };

    unless $found_offset {
        return Nil;
    };

    $fh.seek($found_offset, SeekFromEnd);
    my %ecd = <
        signature
        disknum
        cdir-start-disk
        cdir-on-this-disk
        cdir-total
        cdir-size
        cdir-offset
        comment-length
    > «=>» read-types($fh, int32, int16, int16, int16, int16, int32, int32, int16);
    if %ecd<comment-length> {
        my $comment-buf = $fh.read(%ecd<comment-length>);
        %ecd<comment> = $comment-buf.decode('UTF-8');
    }
    return %ecd;
}


sub read-types($fh, *@types) {
    my @res;
    for @types -> $type {
        my $buf = $fh.read($type.^nativesize/8);
        push @res, [+] $buf.list >>*>> (2**0, 2**8, 2**16, 2**24);
    }
    @res;
}
