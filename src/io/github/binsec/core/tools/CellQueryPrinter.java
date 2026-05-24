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

package io.github.binsec.core.tools;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import io.github.binsec.core.acqvariable.CellType;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.learner.ACQ_Query;

public class CellQueryPrinter extends QueryPrinter {

	CellType[] types;
	boolean[] globals;
	
	public CellQueryPrinter(CellType[] types, boolean[] globals) {
		this.types = types;
		this.globals = globals;
	}
	
	@Override
	public String toString(ACQ_Query q) {
		ArrayList<String> res = new ArrayList<>();
		
		Bitvec[] values = q.getTuple();
		
		int typeindex = 0;
		int i = 0;
		while (i < values.length) {
			String ref = "_";
			if (this.globals[typeindex]) {
				ref = "@"+values[i].unsigned();
				i++;
			}
			switch (types[typeindex]) {
			case STR:
				String cell = "(" + ref + ", ";
				
				if (values[i].equals(Bitvec.zero(values[i].size))) cell += "NL";
				else cell += "@"+values[i].unsigned();
				i++;
				
				Bitvec[] divrem = values[i].divideAndRemainder(new Bitvec(BigInteger.valueOf(1000), values[i].size));
				Bitvec mul = divrem[0];
				Bitvec rem = divrem[1];
				
				// Pretty print string size
				String v = "";
				String strmul = mul.equals(Bitvec.zero(mul.size))? "" : mul.equals(Bitvec.one(mul.size))? "S" : mul.unsigned()+ " * S";
				if (rem.equals(Bitvec.zero(rem.size)) && mul.equals(Bitvec.zero(mul.size))) v = 0+"";
				else if (rem.equals(Bitvec.zero(rem.size))) v = strmul;
				else v = strmul + (mul.equals(Bitvec.zero(mul.size)) ? "" : " + ") + rem.unsigned();
				cell += ", " + v + ")";
				res.add(cell);
				break;
			case INT:
			case INT8:
				res.add("(" + ref + ", " + values[i].signed() + ")");
				break;
				
			
			case PTR:
			case UINT:
			case UINT8:
			case UINT16:
			case BOOL:
				res.add("(" + ref + ", " + values[i].unsigned() + ")");
				break;
			default:
				assert false;
				break;
			}
			i++;
			typeindex++;
		}
		
		return q.getScope() + "::[" + String.join(", ", res) + "]";
	}
}
