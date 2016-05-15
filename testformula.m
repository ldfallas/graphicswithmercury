
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
:- import_module parser.
:- import_module maybe.
:- import_module map.
:- import_module term.
:- import_module term_io.
:- import_module list.
:- import_module string.

:- func mandel_proc(float::in, float::in,float::in, float::in, int::in) = (int::out) is det.

mandel_proc(X,Y,X0,Y0,C) = R  :- 
   (if (X*X + Y*Y < 4.0, C < 255) then
       R = mandel_proc(X*X - Y*Y + X0, 2.0*X*Y + Y0, X0,Y0, C + 1)
    else
       R = C).

:- func mandel(float::in, float::in ) = (int::out) is det.

mandel(X,Y) = R  :- 
   R = mandel_proc(0.0,0.0, X, Y,0).

:- func custom_func_from_expr(expression::in,
                              int::in,
                              float::in, 
                              float::in) = (int::out) is det.

custom_func_from_expr(Expr, MaxEscapeTime, X, Y ) = C :-
    Env0 = map.from_corresponding_lists(
                  ["c"],
                  [mcomplex(X, Y)]),
    C = custom_func_proc(Expr, MaxEscapeTime, 0.0, 0.0, Env0, 0).

:- func custom_func_proc(expression::in, 
                         int::in,
                         float::in, 
                         float::in,                          
                         map(string, mcomplex)::in, 
                         int::in) = (int::out) is det.

custom_func_proc(Expr, MaxEscapeTime, X, Y, Env0, C) = R  :- 
   Env1 = map.det_insert(Env0, "z", mcomplex(X, Y)),
   (if (X*X + Y*Y < 4.0, C < MaxEscapeTime) then
       (if evaluate_complex(
             Expr,
             Env1,
             ok(mcomplex(NX,NY))) then
           R = custom_func_proc(Expr, MaxEscapeTime, NX, NY, Env0, C + 1)
        else 
           R = MaxEscapeTime)
    else
       R = C).


:- type fractal_configuration --->
    config( { int, int },             % image resolution
            { float, float },         % top left cartesian coordinates
            { float, float },         % bottom right cartesian coordinates
            expression,                     % formula
            array({ int, int, int })). % palette


:- pred error_message_with_location(
	    string::in,
	    term(string)::in,
	    string::out) is det.

error_message_with_location(Msg, functor(_,_, context(_,Line)), ResultMsg) :-
     string.append(", at line:",string.int_to_string(Line),TmpString),
     string.append(Msg, TmpString, ResultMsg).
error_message_with_location(Msg, variable(_, context(_,Line)), ResultMsg) :-
     string.append(", at line:",string.int_to_string(Line),TmpString),
     string.append(Msg, TmpString, ResultMsg).

:- pred term_to_fractal_configuration( 
	    term(string)::in, 
	    maybe_error(fractal_configuration)::out) is det.

term_to_fractal_configuration(Term, Result) :-
    (if Term = functor(atom("fractal_config"),Args,_) then
        term_to_fractal_config_resolution(Args, Result)
     else 
        error_message_with_location("Expecting 'fractal_config'",Term, Message),
        Result = error(Message)
    ).

:- pred term_to_palette_config(
	    term(string)::in, 
	    maybe_error(array({ int, int, int }))::out) is det.

term_to_palette_config(Term, Result) :-
   (if Term = functor(atom("palette"),Parts,_) then
       terms_to_palette(Parts, [], Result)
    else
       Result = error("error expecting palette")).

:- pred gen_colors_for_range(int::in, 
                             int::in, 
			     ((func int) = int )::in,
			     ((func int) = int )::in,
			     ((func int) = int )::in,
			     list({int,int,int})::in,
			     list({int,int,int})::out) is det.
gen_colors_for_range(Index, Count, R2RFunc, G2GFunc, B2BFunc, Current, Result) :-
  (if Index > Count then
      Result = Current
      else
        NewCurrent = [{R2RFunc(Index), G2GFunc(Index), B2BFunc(Index)}|Current],
        gen_colors_for_range(Index + 1, Count, R2RFunc, G2GFunc, B2BFunc, NewCurrent, Result)).

:- pred terms_to_palette(
	    list(term(string))::in, 
            list({int, int, int})::in,
	    maybe_error(array({int,int,int}))::out) is det.

terms_to_palette([],TmpResult, ok(ResultArray)) :-
   list.reverse(TmpResult, ReversedList),
   array.from_list(ReversedList, ResultArray).

terms_to_palette([Term|Rest],TmpResult,Result) :-
   (if Term = functor(atom("single"),
                     [functor(integer(R),_,_),
                      functor(integer(G),_,_),
		      functor(integer(B),_,_)],
                     _) then
       terms_to_palette(Rest, [{R,G,B}|TmpResult], Result)
     else
      (if Term = functor(atom("range"),[
                            functor(atom("from"),
                                    [functor(integer(R1),_,_),
                                     functor(integer(G1),_,_),
	            	             functor(integer(B1),_,_)],_),
                            functor(atom("to"),
                                    [functor(integer(R2),_,_),
                                     functor(integer(G2),_,_),
	            	             functor(integer(B2),_,_)],_),
                            functor(integer(Count),_,_)
                         ],_) then
           int_interpolate_funcs(R1, R2,1, Count, _, R2RFunc),
           int_interpolate_funcs(G1, G2,1, Count, _, G2GFunc),
           int_interpolate_funcs(B1, B2,1, Count, _, B2BFunc),
           gen_colors_for_range(1, Count, R2RFunc, G2GFunc, B2BFunc,[], RangeList),
           list.append(TmpResult, RangeList,  NewTmpResult),
           terms_to_palette(Rest, NewTmpResult, Result)
       else
           Result = error("Problem reading palette configuration"))
).



:- pred term_to_fractal_config_resolution(
	    list(term(string))::in, 
	    maybe_error(fractal_configuration)::out).
term_to_fractal_config_resolution(Terms, Result) :-
   (if Terms = [functor(atom("image_resolution"),
                     [ functor(integer(Width),_, _),
		       functor(integer(Height),_, _) ],
		     _)|Rest1] then
       (if  Rest1 = [functor(atom("top_left"),
                     [ functor(float(LeftX),_,_),
		       functor(float(TopY),_,_) ],
		     _)|Rest2] then
		(if  Rest2 = [functor(atom("bottom_right"),
                     [ functor(float(RightX),_,_),
		       functor(float(BottomY),_,_) ],
		     _)|Rest3] then
                    
                    (if Rest3 = [functor(atom("formula"),[Term],_)|Rest4],term_to_expression(Term, ok(Expr)) then
                        (if Rest4 = [PaletteConfig], term_to_palette_config(PaletteConfig, ok(Palette)) then 
                              Result  = ok(config( { Width, Height },
                                                   { LeftX, TopY },
                                                   { RightX, BottomY },
                                                   Expr,
                                                   Palette
 ))
                          
                           else
                              Result = error("Error reading palette")
                        )
                    else
                      Result = error("Error reading formula"))
                 else
                    Result = error("Error expecting: bottom_right(float,float)")
        )

        else
           Result = error("Error expecting: top_left(float,float)")
        )
    else
       Result = error("Error expecting: image_resolution(int,int)")
    ).


:- pred read_fractal_configuration_from_file( 
            string::in, 
            maybe_error(fractal_configuration)::out, 
            io::di, io::uo) is det.

read_fractal_configuration_from_file(FileName, ConfigurationResult, !IO) :-
    parser.read_term_filename( FileName,  ReadTermResult, !IO),
    ((ReadTermResult = term(_, Term),
         term_to_fractal_configuration(Term, ConfigurationResult))
      ; (ReadTermResult = error(ErrMessage, _),
          ConfigurationResult = error(ErrMessage))
      ; (ReadTermResult = eof,
          ConfigurationResult = error("Empty file"))
     ).
  


main(!IO) :-
   io.command_line_arguments(Args,!IO),
   (if Args = [InputFileName] then
      io.open_input(InputFileName, StreamResult, !IO),
      (if (StreamResult = ok(Stream)) then
         io.set_input_stream(Stream,_, !IO),
         read_fractal_configuration_from_file(InputFileName, ConfigResult, !IO),
         (if ConfigResult = ok(config({Width, Height}, {LeftX, TopY},{RightX, BottomY},Expr,Palette)) then
            io.write_string("Creating matrix data...",!IO),
            io.nl(!IO),
            init_rectangular_array( 
                { Width, Height }, 
                { LeftX, BottomY }, %% workaround for BMP layout
                { RightX, TopY },
                custom_func_from_expr(Expr, array.size(Palette) - 1 ),
                IndexArray),
            io.write_string("Creating bitmap data...",!IO),
            io.nl(!IO),
            index_array_to_bitmap_array(
                IndexArray, 
                Palette,
                BitMapArray),
            io.write_string("Creating file.bmp ...", !IO),
            io.nl(!IO),
            bmp.write_bmp("file.bmp", Width, Height, BitMapArray,!IO ),
            io.write("Done!", !IO)

          else
            io.write(ConfigResult, !IO)
         )
         
       else
          io.write(StreamResult ,!IO))
    else io.write("Incorrect number of arguments, expecting fractal configuration file name.",!IO)),

   io.nl(!IO).
