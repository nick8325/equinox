%--------------------------------------------------------------------------
% File     : HWV038-1 : TPTP v5.1.0. Released v2.5.0.
% Domain   : Hardware Verification
% Problem  : Axioms from a VHDL design description
% Version  : [Mar02] axioms : Especial.
% English  :

% Refs     : [CHM02] Claessen et al. (2002), Verification of Hardware Systems
%          : [Mar02] Martensson (2002), Email to G. Sutcliffe
% Source   : [Mar02]
% Names    :

% Status   : Satisfiable
% Rating   : 1.00 v3.2.0, 0.80 v3.1.0, 0.67 v2.6.0, 1.00 v2.5.0
% Syntax   : Number of clauses     :  133 (  62 non-Horn;  25 unit;  92 RR)
%            Number of atoms       :  415 (  80 equality)
%            Maximal clause size   :   10 (   3 average)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :   45 (   7 constant; 0-3 arity)
%            Number of variables   :  225 (  20 singleton)
%            Maximal term depth    :    5 (   2 average)
% SPC      : CNF_SAT_RFO_EQU_NUE

% Comments : Infinox says this has no finite (counter-) models.
%--------------------------------------------------------------------------
%----Include Axioms from a VHDL design description
include('Axioms/HWV004-0.ax').
%--------------------------------------------------------------------------
