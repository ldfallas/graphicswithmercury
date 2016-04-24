:- module formulaspec.

:- interface.

:- import_module io.
:- import_module array.
:- import_module map.
:- import_module maybe.
:- import_module term.

:- pred term_to_expression(term::in, maybe_error(expression)::out) is det.

:- type operator ---> times ; plus ; minus ; division.

:- type expression ---> 
     literal_num(float)
     ; var(string)
     ; imaginary
     ; bin_operation(expression, operator, expression).


:- type mcomplex ---> mcomplex(float, float).

:- pred evaluate_complex(expression::in, 
                 map(string, mcomplex)::in, 
                 maybe_error(mcomplex)::out) is det.


:- pred kmain(io::di, io::uo) is cc_multi.

:- pred init_rectangular_array( 
	    {int, int}::in, 
	    {float, float}::in,
	    {float, float}::in,
	    (func(float,float) = int)::in,
	    array(int)::out) is det.


:- pred interpolate_funcs(float::in, float::in, 
                       int::in, int::in,
		      ((func float) = int )::out,
		      ((func int) = float )::out) is det.

:- pred index_array_to_bitmap_array(
            array(int)::in, 
            array({ int, int, int })::in,
            array(int)::out) is det.



:- implementation.
:- import_module term_io.
:- import_module string.
:- import_module float.
:- import_module list.
:- import_module array.
:- import_module int.

:- pred const_to_s(const::in, string::out) is det.
:- pred term_to_s(term::in,string::out) is det.

term_to_s(functor(C,L,_), Str) :-
   const_to_s(C,OStr),
   string.append("FUNCTORTERM",OStr,Str).
term_to_s(variable(_,_), Str) :-
   string.append("VARIABLE","STR",Str).

const_to_s(atom(AtomVal), Str) :-
   string.append("ATOM_",AtomVal,Str).
const_to_s(integer(_), Str) :-
   string.append("INT_","Int",Str).
const_to_s(big_integer(_,_), Str) :-
   string.append("Big_","Int",Str).
const_to_s(string(AStr), Str) :-
   string.append("STR_",AStr,Str).
const_to_s(float(_), Str) :-
   string.append("FLT_","",Str).
const_to_s(implementation_defined(_), Str) :-
   string.append("OTHER_","",Str).
   




%:- pred term_to_expression(term::in, maybe_error(expression)::out) is cc_multi.

%% term_to_expression(functor(atom("+"),[Op1,Op2],_), Expr) :-
%%    term_to_expression(Op1, ok(Op1Expr)),
%%    term_to_expression(Op2, ok(Op2Expr)),
%%    Expr = ok(bin_operation(Op1Expr, plus, Op2Expr)).
%% term_to_expression(functor(float(X),[],_), Expr) :-
%%    Expr = ok(literal_num(X)).
%% term_to_expression(_, error("Error")).

term_to_expression(functor(atom(AtomStr),Ops,_), Expr) :-
   (if (Ops = [Op1,Op2],
        op_to_string(Operator,AtomStr),
        term_to_expression(Op1, ok(Op1Expr)),
        term_to_expression(Op2, ok(Op2Expr))) then
      Expr = ok(bin_operation(Op1Expr, Operator, Op2Expr))
    else
      (if Ops = [] then
          Expr = ok(var(AtomStr))
       else
          Expr = error("Error"))
   ).
term_to_expression(functor(float(X),_,_), Expr) :-
   Expr = ok(literal_num(X)).
term_to_expression(functor(integer(X),_,_), Expr) :-
   Expr = ok(literal_num(float(X))).
term_to_expression(functor(big_integer(_,_),_,_), error("Error")).
term_to_expression(functor(string(_),_,_), error("Error")).
term_to_expression(functor(implementation_defined(_),_,_), error("Error")).
term_to_expression(variable(_,_), error("Error")).


%term_to_expression(_, error("Error")).


:- pred op_to_string(operator,string).
:- mode op_to_string(in,out) is det.
:- mode op_to_string(out, in) is semidet.

op_to_string(times,"*").
op_to_string(minus,"-").
op_to_string(plus,"+").
op_to_string(division,"/").

:- pred expr_to_string(expression::in,string::out) is det.

expr_to_string(literal_num(X), Str) :-
   Str = string.from_float(X).

expr_to_string(var(X), Str) :-
   Str = X.

expr_to_string(imaginary, Str) :-
   Str = "i".

expr_to_string(bin_operation(E1, Op, E2), Str) :-
   op_to_string(Op,StrOp),
   expr_to_string(E1, StrE1),
   string.append(StrE1,StrOp,Tmp1),
   expr_to_string(E2, StrE2),
   string.append(Tmp1,StrE2,Str).


:- pred simplify2(expression::in, expression::out) is cc_multi.

simplify2(bin_operation(X, Op, Y), Result) :-
   simplify2(X,Xsimplified),
   simplify2(Y,Ysimplified),
   simplifying2(bin_operation(Xsimplified, Op, Ysimplified), Result).

simplify2(Result, Result).


:- pred simplifying2(expression::in, expression::out) is cc_multi.

simplifying2(bin_operation(var(X), times, literal_num(Y)), 
	     bin_operation( literal_num(Y), times,var(X))).

simplifying2(bin_operation(var(X), times, literal_num(0.0)), 
	     literal_num(0.0)).

simplifying2(bin_operation(literal_num(X), times, literal_num(Y)), 
	     literal_num(X*Y)).

simplifying2(bin_operation(literal_num(X), plus, literal_num(Y)), 
	     literal_num(X+Y)).

simplifying2(bin_operation(bin_operation(X, plus, literal_num(Y)), plus, literal_num(Z)), 
             Result) :-
   simplifying2(bin_operation(X, plus, literal_num(Y+Z)),
	       Result).

simplifying2(bin_operation(X, times, bin_operation(Y, plus, Z)), 
             Result) :-
   simplifying2(bin_operation(X, times,Y), Left),
   simplifying2(bin_operation(X, times,Z), Right),
   simplifying2(bin_operation(Left,plus, Right),
	       Result).

simplifying2(bin_operation(bin_operation(X, plus, Y), times, Z), 
             Result) :-
   simplifying2(bin_operation(X, times,Z), Left),
   simplifying2(bin_operation(Y, times,Z), Right),
   simplifying2(bin_operation(Left,plus, Right),
	       Result).


simplifying2(X,X).

:- pred simplify(expression::in, expression::out) is cc_multi.

simplify(bin_operation(var(X), times, bin_operation(E1,plus,E2)), Result) :-
    simplify(bin_operation(var(X), times, E1),Op1),
    simplify(bin_operation(var(X), times, E2),Op2),
    simplify(
         bin_operation(Op1, plus, Op2),
         Result).

simplify(bin_operation(literal_num(X), times, literal_num(Y)), Result) :-
    simplify(literal_num(X*Y), Result).

simplify(bin_operation(_, times, literal_num(0.0)),
         literal_num(0.0)).
simplify(bin_operation(literal_num(0.0),times,_ ),
         literal_num(0.0)).

simplify(bin_operation(Op1, plus, literal_num(0.0)),Op1).
simplify(bin_operation(literal_num(X), plus, literal_num(Y)),literal_num(Result)) :- 
    Result = X+Y.
simplify(bin_operation(literal_num(X), times, literal_num(Y)),literal_num(Result)) :-
    Result = X*Y.

simplify(bin_operation(literal_num(0.0), plus, Op1),Op1).


simplify(X,X).


:- pred reduce_expression(expression::in,map(string,expression)::in, expression::out) is det.

reduce_expression(var(VarName), Env, Result) :-
   (if map.search(Env, VarName, LookupResult) then
       reduce_expression(LookupResult, Env, Result)
    else
       Result = var("ERROR")).

reduce_expression(literal_num(X), Env, literal_num(X)).

reduce_expression(imaginary, _, imaginary).

reduce_expression(bin_operation(Left, Operator, Right), Env, Result) :-
   reduce_expression(Left, Env, LeftReduced),
   reduce_expression(Right, Env, RightReduced),
   NewBinaryOperation =  bin_operation(LeftReduced, Operator, RightReduced),
   (   NewBinaryOperation = bin_operation(literal_num(X1), times, literal_num(X2)) ->
              Result = literal_num(X1 * X2)
      ;   NewBinaryOperation = bin_operation(literal_num(X1), plus, literal_num(X2)) ->
              Result = literal_num(X1 + X2)
      ;   NewBinaryOperation = bin_operation(literal_num(X1), division, literal_num(X2)) ->
              Result = literal_num(X1 / X2)
      ;   NewBinaryOperation = bin_operation(literal_num(X1), minus, literal_num(X2)) ->
              Result = literal_num(X1 - X2)
      ;   NewBinaryOperation = bin_operation(imaginary, times, imaginary) ->
              Result = literal_num(-1.0)
      ;   NewBinaryOperation = bin_operation(imaginary, Op, literal_num(X)) ->
              Result = bin_operation(literal_num(X),Op,imaginary)
      ;  NewBinaryOperation = bin_operation( bin_operation(X2, plus, X3),times,X1) ->
              Op1 = bin_operation(X1, times, X2),
              Op2 = bin_operation(X1, times, X3),
              reduce_expression(bin_operation(Op1, plus, Op2), Env, Result)
      ;  NewBinaryOperation = bin_operation(X1, times, bin_operation(X2, plus, X3)) ->
              Op1 = bin_operation(X1, times, X2),
              Op2 = bin_operation(X1, times, X3),
              reduce_expression(bin_operation(Op1, plus, Op2), Env, Result)
      ;  NewBinaryOperation = bin_operation(literal_num(X1), plus, bin_operation(X2, plus, literal_num(X3))) ->
              reduce_expression(bin_operation(X2, plus, literal_num(X1+X3)),Env,Result)
      ;  NewBinaryOperation = bin_operation(literal_num(X1), plus, bin_operation(literal_num(X2), plus, X3)) ->
              reduce_expression(bin_operation(X3, plus, literal_num(X1+X2)), Env, Result)
      ;  NewBinaryOperation = 
            bin_operation(
                  bin_operation(literal_num(X1), plus, bin_operation(literal_num(X2), times, imaginary)),
                  plus,
                  bin_operation(literal_num(X4), plus, bin_operation(literal_num(X5), times, imaginary))) ->
              reduce_expression(bin_operation(literal_num(X1+X4), 
                                plus, 
                                bin_operation(literal_num(X5+X2), times, imaginary)), Env, Result)
      ;
         Result = bin_operation(LeftReduced, Operator, RightReduced) ).

%% :- type operator ---> times ; plus ; minus ; division.

%% :- type expression ---> 
%%      literal_num(float)
%%      ; var(string)
%%      ; bin_operation(expression, operator, expression).

:- pred apply_operator(operator::in, float::in, float::in, float::out).

apply_operator(times, X, Y, Result) :- Result = X * Y.
apply_operator(plus , X, Y, Result) :- Result = X + Y.
apply_operator(minus, X, Y, Result) :- Result = X - Y.
apply_operator(division, X, Y, Result) :- Result = X / Y.


:- pred evaluate(expression::in, 
                 map(string, float)::in, 
                 maybe_error(float)::out) is det.

evaluate(literal_num(Number), _, ok(Number)).

evaluate(imaginary, _, error("imaginary")).


evaluate(var(Variable), Vars, Result) :-
   (if map.search(Vars, Variable, Value) then
      Result = ok(Value)
    else
      Result = error(append("Variable not found: ",Variable))
    ).

evaluate(bin_operation(Expr1,Operator,Expr2), Vars, Result) :-
     evaluate(Expr1, Vars, LeftResult),
     evaluate(Expr2, Vars, RightResult),
     (if LeftResult = ok(LeftValue) then
         (if RightResult = ok(RightValue) then
            apply_operator(Operator, LeftValue,RightValue, OperationResult),
            Result = ok(OperationResult)
          else
            Result = RightResult)
      else
         Result = LeftResult
      ).





:- pred apply_complex_operator(operator::in, mcomplex::in, mcomplex::in, mcomplex::out).


%a+bi * 1/(x + yi)
%ab - by + (ay + xb)i 
apply_complex_operator(times, mcomplex(X1,X2), mcomplex(Y1,Y2), Result) :- Result = mcomplex(X1*Y1 - Y2*X2, X1*Y2 + X2*Y1).
apply_complex_operator(plus , mcomplex(X1,X2), mcomplex(Y1,Y2) , Result) :- Result = mcomplex(X1 + Y1, X2 + Y2).
apply_complex_operator(minus, mcomplex(X1,X2), mcomplex(Y1,Y2) , Result) :- Result = mcomplex(X1 - Y1, X2 - Y2).
apply_complex_operator(division, mcomplex(X1,X2), mcomplex(Y1,Y2) , Result) :- 
   Result = mcomplex((X1*X2 + Y1*Y2) / (Y1*Y1 + Y2*Y2),
                     (Y1*X1 - X1*Y2) / (Y1*Y1 + Y2*Y2)).


%%
%% complex expression evaluation
%%

evaluate_complex(literal_num(Number), _, ok(mcomplex(Number,0.0))).

evaluate_complex(imaginary, _, ok(mcomplex(0.0, 1.0))).


evaluate_complex(var(Variable), Vars, Result) :-
   (if map.search(Vars, Variable, Value) then
      Result = ok(Value)
    else
      Result = error(append("Variable not found: ",Variable))
    ).

evaluate_complex(bin_operation(Expr1,Operator,Expr2), Vars, Result) :-
     evaluate_complex(Expr1, Vars, LeftResult),
     evaluate_complex(Expr2, Vars, RightResult), (if LeftResult =
     ok(LeftValue) then (if RightResult = ok(RightValue) then
     apply_complex_operator(Operator, LeftValue,RightValue,
     OperationResult), Result = ok(OperationResult) else Result =
     RightResult) else Result = LeftResult ).


interpolate_funcs(FromF, ToF, FromI, ToI,
              FloatToIntFunc,
              IntToFloatFunc) :-
    M1 = (float(ToI) - float(FromI))/(ToF  - FromF),
    B1 = float(FromI)  - M1*FromF,
    M2 = (ToF - FromF)/(float(ToI) - float(FromI)),
    B2 = FromF - M2*float(FromI),
    FloatToIntFunc = (func(X::in) = (Y::out) is det :- Y =  truncate_to_int(M1*X + B1)),
    IntToFloatFunc = (func(X::in) = (Y::out) is det :- Y =  (M2*float(X) + B2)).


init_rectangular_array( {PixWidth, PixHeight},
                        {X1,Y1}, 
                        {X2,Y2},
			InitPixFunc,
			ResultArray) :-
    interpolate_funcs(X1, X2, 0, PixWidth, _, WI2F),
    interpolate_funcs(Y1, Y2, 0, PixHeight, _, HI2F),
    ResultArray = array.generate(PixWidth * PixHeight,
		   func(Index::in) = (ResultIndex::out) is det :- 
                         ResultIndex = InitPixFunc(
                             WI2F(Index mod PixWidth), 
                             HI2F(Index / PixWidth ))).


index_array_to_bitmap_array(IndexArray, Palette, BitmapArray) :-
    array.size(IndexArray, Size),
    BitmapArray = 
       array.generate(Size * 3, 
		     (func(Index) = Result :- 
                         Entry = array.elem(Index / 3, IndexArray),
			 {R, G, B} = array.elem(Entry, Palette),
		         Channel = Index mod 3,
			 (if Channel = 0 then
                             Result = R
                          else (if Channel = 1 then
                                   Result = G
                                else
                                   Result = B)))).


kmain(!IO) :-
   interpolate_funcs(-1.0, 1.0, 0, 5, F2I, _),
   io.write(F2I(1.0), !IO),
   io.write(",",!IO),
   io.nl(!IO),
   io.write(F2I(0.0), !IO),
   io.write(",",!IO),
   io.nl(!IO),
   io.write(F2I(-1.0), !IO),
   io.write(",",!IO),
   io.nl(!IO),

   Expr1 = bin_operation(var("x"), times, bin_operation(literal_num(4.0),times,literal_num(2.0))),
   simplify2(Expr1,Expr),
   expr_to_string(Expr, S),
   io.write_string(S,!IO),
   io.nl(!IO),
   term_io.read_term(T, !IO),
   (if T = term(V1,Trm1) then
      term_to_expression(Trm1, Exprs1),
      ( if (Exprs1 = ok(Expr2)) then 
          simplify2(Expr2,Expr3),
          expr_to_string(Expr3,Str2),
          io.write_string(Str2,!IO),
          io.nl(!IO),
          evaluate(Expr3,map.from_corresponding_lists(["x"],[102.3]), Result),
          io.write(Result,!IO),
          io.nl(!IO),

          evaluate_complex(Expr3,map.from_corresponding_lists(["x"],[mcomplex(1.2,102.3)]), ResultC),
          io.write(ResultC,!IO),
          io.nl(!IO),


          reduce_expression(Expr2,map.from_corresponding_lists(["x"],[bin_operation(literal_num(102.3),plus,imaginary)]), ResultReduced),
          io.write(ResultReduced,!IO)

        else
          io.write_string("Recog error",!IO))
      else
         io.write_string("Term error",!IO)),
   (if T = term(V,Trm) then
     term_to_s(Trm,Str),
     io.write_string(Str,!IO),
     term_io.write_term(V,Trm, !IO)
    else
       (if T = error(Str,_) then
           io.write_string(Str,!IO)
        else
           io.write_string("Nel",!IO))
    ).

