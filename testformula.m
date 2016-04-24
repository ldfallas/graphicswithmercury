:- module testformula.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module bmp.
:- import_module int.
:- import_module array.
:- import_module formulaspec.
:- import_module float.
:- import_module list.

main(!IO) :-
   io.write_string("Creating matrix data...",!IO),
   io.nl(!IO),
   Width = 320,
   Height = 200,
   init_rectangular_array( 
	    {Width, Height}, 
	    {-1.0, 1.0},
	    {1.0, -1.0},
	    (func(X, Y) = R :- 
                 (if X*X + Y*Y < 0.5 then 
                     R = 1 
                  else 
                     R = 0)),
	    IndexArray),


   io.write_string("Creating bitmap data...",!IO),

   index_array_to_bitmap_array(
            IndexArray, 
            array([{0 ,0, 0}, {255,0,0}]),
            BitMapArray),

   io.write_string("Creating file.bmp ...", !IO),


   bmp.write_bmp("file.bmp", Width, Height, BitMapArray,!IO ),
 
   io.write("Done!", !IO),
   io.nl(!IO).
