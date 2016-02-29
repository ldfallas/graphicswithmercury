:- module bmp.

:- interface.

:- import_module io.
:- import_module array.
 
:- pred write_bmp(string::in,
        int::in, 
        int::in, 
        array(int)::in,
        io::di, io::uo) is det.


:- implementation.

:- import_module char.


:- import_module io.
:- import_module int.
:- import_module float.
:- import_module array.

:- pred write_int(io.binary_output_stream::in,int::in, io::di, io::uo) is det.
write_int(Stream,IntValue,!IO) :-
   io.write_byte(Stream, IntValue /\ 0xFF,!IO),
   io.write_byte(Stream, (IntValue >> 8) /\ 0xFF,!IO),
   io.write_byte(Stream, (IntValue >> 16) /\ 0xFF,!IO),
   io.write_byte(Stream, (IntValue >> 24) /\ 0xFF,!IO).

:- pred write_short(int::in,io.binary_output_stream::in, io::di, io::uo) is det.
write_short(IntValue,Stream,!IO) :-
   io.write_byte(Stream, IntValue /\ 0xFF,!IO),
   io.write_byte(Stream, (IntValue >> 8) /\ 0xFF,!IO).





:- pred write_pixel_data(
        io.binary_output_stream::in,
	array(int)::in,
        int::in,  % width
        int::in,  % height
        int::in,  % padding
        int::in,  % idx
        io::di, io::uo) is det.
write_pixel_data(Stream,
                 Data,
                 Width,
                 Height,
                 Padding,
                 Index,
                 !IO) :-
     Div = Index / (Width + Padding),
     Mod = Index mod (Width + Padding),
     (if Mod > (Width - 1) then 
         io.write_byte(Stream, 0, !IO)
      else
         io.write_byte(Stream,array.lookup(Data,Index - (Div*Padding)),!IO)) .

write_bmp(Name, Width, Height,ImgData, !IO) :- 
    RowWidth = floor_to_int((float(Width)*24.0 + 31.0)/32.0)*4,
    io.write_int(RowWidth,!IO),
    io.open_binary_output(Name,StreamRes,!IO),
    (if StreamRes = ok(Stream) then
       io.write_byte(Stream,char.to_int('B'),!IO),
       io.write_byte(Stream,char.to_int('M'),!IO),
       %  write the size 
       write_int(Stream, 40 + 14 + RowWidth*Height,!IO),
       % write reserved1
       io.write_byte(Stream,0,!IO),
       io.write_byte(Stream,0,!IO),
       % write reserved2
       io.write_byte(Stream,0,!IO),
       io.write_byte(Stream,0,!IO),
       % write the offset
       write_int(Stream,40 + 14, !IO),
       % write DIB header
       io.write_byte(Stream,40,!IO),
       io.write_byte(Stream,0,!IO),
       io.write_byte(Stream,0,!IO),
       io.write_byte(Stream,0,!IO),       
       write_int(Stream,Width, !IO),
       write_int( Stream,Height, !IO),
       % Color planes
       write_short(1, Stream, !IO),
       % Bpp
       write_short(24, Stream, !IO),
       % Compression
       write_int(Stream,0,!IO),
       % Bitmap data size
       write_int(Stream, RowWidth*Height, !IO),
       % px/metter
       write_int(Stream, 2835, !IO),
       % px/metter
       write_int(Stream, 2835, !IO),
       % Palette size
       write_int(Stream,0,!IO),
       % important colors
       write_int(Stream,0,!IO),

       %WritePixel = (pred(I::in,!.IO::di,!:IO::uo) :-
       %   1 = 1.
       %),
       io.write_int(RowWidth,!IO),
       int.fold_up(write_pixel_data(Stream,
                 ImgData,
                 Width * 3,
                 Height,
                 (RowWidth - (Width * 3))),0,(RowWidth*Height) - 1,!IO)

       else
          io.write_string("error",!IO)).

