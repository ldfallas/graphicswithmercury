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
:- import_module parser.
:- import_module maybe.
:- import_module map.
:- import_module term.
:- import_module term_io.

:- func mandel_proc(float::in, float::in,float::in, float::in, int::in) = (int::out) is det.

mandel_proc(X,Y,X0,Y0,C) = R  :- 
   (if (X*X + Y*Y < 4.0, C < 255) then
       R = mandel_proc(X*X - Y*Y + X0, 2.0*X*Y + Y0, X0,Y0, C + 1)
    else
       R = C).

:- func mandel(float::in, float::in ) = (int::out) is det.

mandel(X,Y) = R  :- 
   R = mandel_proc(0.0,0.0, X, Y,0).

:- func custom_func_from_expr(expression::in,float::in, float::in) = (int::out) is det.

custom_func_from_expr(Expr, X,Y ) = C :-
    C = custom_func_proc(Expr, 0.0, 0.0, mcomplex(X, Y),0).

:- func custom_func_proc(expression::in, float::in, float::in, mcomplex::in, int::in) = (int::out) is det.

custom_func_proc(Expr,X,Y,XY0,C) = R  :- 
   (if (X*X + Y*Y < 4.0, C < 255) then
       (if evaluate_complex(
             Expr,
             map.from_corresponding_lists(
                  ["z","c"],
                  [mcomplex(X,Y), XY0]),
             ok(mcomplex(NX,NY))) then
           R = custom_func_proc(Expr, NX, NY,XY0, C + 1)
        else 
           R = 255)
    else
       R = C).


main(!IO) :-
   io.write_string("Creating matrix data...",!IO),
   io.nl(!IO),
   Width = 320,
   Height = 200,
   parser.read_term_from_string("f.m","z*z*z + c.",_,ReadTermResult),
   (if ReadTermResult = term(_, Term),
      term_to_expression(Term, ok(Expr)) then
      init_rectangular_array( 
	    {Width, Height}, 
	    {-1.0, 1.0},
	    {1.0, -1.0},
            custom_func_from_expr(Expr),
            %%mandel,
	    %% (func(X, Y) = R :- 
            %%      (if X*X + Y*Y < 0.5 then 
            %%          R = 1 
            %%       else 
            %%          R = 0)),
	    IndexArray),

      io.write_string("Creating bitmap data...",!IO),

      index_array_to_bitmap_array(
            IndexArray, 
            array.generate(256, (func(Index) = R :- R = {Index,255 - Index,0})),
            %array([{0 ,0, 0}, {255,0,0}]),
            BitMapArray),

      io.write_string("Creating file.bmp ...", !IO),


      bmp.write_bmp("file.bmp", Width, Height, BitMapArray,!IO ),
 
      io.write("Done!", !IO)
   else 
      io.write(ReadTermResult,!IO),
      io.write_string("Error reading term",!IO)),
   io.nl(!IO).
