/****************************************************************************/
/*  This file is part of PRECA.                                             */
/*  PRECA is part of the BINSEC toolbox for binary-level program analysis.  */
/*                                                                          */
/*  Copyright (C) 2019-2023                                                 */
/*    CEA (Commissariat à l'énergie atomique et aux énergies                */
/*         alternatives)                                                    */
/*                                                                          */
/*  you can redistribute it and/or modify it under the terms of the GNU     */
/*  Lesser General Public License as published by the Free Software         */
/*  Foundation, version 2.1.                                                */
/*                                                                          */
/*  It is distributed in the hope that it will be useful,                   */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of          */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           */
/*  GNU Lesser General Public License for more details.                     */
/*                                                                          */
/*  See the GNU Lesser General Public License version 2.1                   */
/*  for more details (enclosed in the file licenses/LGPLv2.1).              */
/*                                                                          */
/****************************************************************************/

package io.github.binsec.core.acqconstraint;

import java.util.HashMap;

public enum Operator {

    NONE(), EQ(), LT(), GT(), NQ(), LE(), GE(), PL(), MN(), Dist(), SMOD(), UMOD(), SLT(), SGT(), SLE(), SGE(), ULT(),
    UGT(), ULE(), UGE();

	private static HashMap<String, Operator> operators = new HashMap<>();

    static {
        operators.put("@", Operator.NONE);
        operators.put("=", Operator.EQ);
        operators.put(">", Operator.GT);
        operators.put(">=", Operator.GE);
        operators.put("<", Operator.LT);
        operators.put("<=", Operator.LE);
        
        operators.put("bvslt", Operator.SLT);
        operators.put("bvsle", Operator.SLE);
        operators.put("bvsgt", Operator.SGT);
        operators.put("bvsge", Operator.SGE);
        
        operators.put("bvult", Operator.ULT);
        operators.put("bvule", Operator.ULE);
        operators.put("bvugt", Operator.UGT);
        operators.put("bvuge", Operator.UGE);
        
        operators.put("!=", Operator.NQ);
        operators.put("+", Operator.PL);
        operators.put("-", Operator.MN);
        operators.put("abs", Operator.Dist);
        operators.put("smod", Operator.SMOD);
        operators.put("umod", Operator.UMOD);
    }

	public static Operator get(String name) {
        return operators.get(name);
	}

	@Override
	public String toString() {
		switch (this){
			case LT:return "<";
			case ULT:return "bvult";
			case SLT:return "bvslt";
			
			case GT:return ">";
			case UGT:return "bvugt";
			case SGT:return "bvsgt";
			
			case LE:return "<=";
			case ULE:return "bvule";
			case SLE:return "bvsle";
			
			case GE:return ">=";
			case UGE:return "bvuge";
			case SGE:return "bvsge";
			
			case NQ:return "!=";
			case EQ:return "=";
			case PL:return "+";
			case MN:return "-";
			case Dist:return "dist";
			case SMOD:return "smod";
			case UMOD:return "umod";


			default:throw new UnsupportedOperationException();
		}
	}

	/**
	 * Flips the direction of an inequality
	 * @param operator op to flip
	 */
	public static String getFlip(String operator) {
		switch (get(operator)){
			case LT:return ">";
			case GT:return "<";
			case LE:return ">=";
			case GE:return "<=";
			//default:assert false :"getflip used";return operator;
			default:return operator;
		}
	}

	public static Operator getOpposite(Operator operator) {
		switch (operator){
			case LT:return GE;
			case ULT:return UGE;
			case SLT:return SGE;
			
			case GT:return LE;
			case UGT:return ULE;
			case SGT:return SLE;
			
			case LE:return GT;
			case ULE:return UGT;
			case SLE:return SGT;
			
			case GE:return LT;
			case UGE:return ULT;
			case SGE:return SLT;

			case NQ:return EQ;
			case EQ:return NQ;
			case PL:return PL;			//NL: neutral negation on PL and MN
			case MN:return MN;
			case SMOD:return SMOD;
			case UMOD:return UMOD;

			default:throw new UnsupportedOperationException();
		}
	}
	
	public static Operator getOperator(String s) {
		System.out.println(s);
		switch(s) {
		case("EqualXY"):
			return Operator.EQ;
		case("DiffXY"):
			return Operator.NQ;
		case("GreaterOrEqualXY"):
			return Operator.GE;
		case("GreaterXY"):
			return Operator.GT;
		case("LessOrEqualXY"):
			return Operator.LE;
		case("LessXY"):
			return Operator.LT;
		case("EqualX"):
			return Operator.EQ;
		case("DiffX"):
			return Operator.NQ;
		case("GreaterOrEqualX"):
			return Operator.GE;
		case("GreaterX"):
			return Operator.GT;
		case("LessOrEqualX"):
			return Operator.LE;
		case("LessX"):
			return Operator.LT;
		default:
			return getOperatorUnary(s);
		}
	}
	
	public static Operator getOperatorUnary(String s) {
		if(s.matches("^DiffX.*"))
			return Operator.NQ;
		else if(s.matches("^EqualX.*"))
			return Operator.EQ;
		else if(s.matches("^GreaterOrEqualX.*"))
			return Operator.GE;
		else if(s.matches("^GreaterX.*"))
			return Operator.GT;
		else if(s.matches("^LessOrEqualX.*"))
			return Operator.LE;
		else if(s.matches("^LessX.*"))
			return Operator.LT;
		throw new UnsupportedOperationException();
	}
	
	public static String getName(Operator op) {
		switch (op){
		case LT:
		case ULT:
		case SLT:return "LessXY";
		case GT:
		case UGT:
		case SGT:return "GreaterXY";
		case LE:
		case ULE:
		case SLE:return "LessEqualXY";
		case GE:
		case UGE:
		case SGE:return "GreaterEqualXY";
		case NQ:return "DifferentXY";
		case EQ:return "EqualXY";
		case PL:return null; //TODO
		case MN:return null; // TODO
		
		default:throw new UnsupportedOperationException();
	}
	}
	
	public static String opToSmtlib(Operator op) {
		switch (op) {
		case EQ:
			return "=";
		case NQ:
			return "distinct";

		case GT:
			return ">";
		case SGT:
			return "bvsgt";
		case UGT:
			return "bvugt";

		case GE:
			return ">=";
		case SGE:
			return "bvsge";
		case UGE:
			return "bvuge";

		case LT:
			return "<";
		case SLT:
			return "bvslt";
		case ULT:
			return "bvult";

		case LE:
			return "<=";
		case SLE:
			return "bvsle";
		case ULE:
			return "bvule";

		default:
			assert false : "unknown operator";

		}
		return null;
	}
}
