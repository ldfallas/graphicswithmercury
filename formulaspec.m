:- module formulaspec.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is cc_multi.

:- implementation.
:- import_module term.
:- import_module term_io.
:- import_module string.
:- import_module float.
:- import_module maybe.
:- import_module list.
:- import_module map.

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
   

:- type operator ---> times ; plus ; minus ; division.

:- type expression ---> 
     literal_num(float)
     ; var(string)
     ; bin_operation(expression, operator, expression).


:- pred term_to_expression(term::in, maybe_error(expression)::out) is det.
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




main(!IO) :-
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
          io.write(Result,!IO)
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

