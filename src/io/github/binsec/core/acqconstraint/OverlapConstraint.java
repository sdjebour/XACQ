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

import java.util.Map;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.acqvariable.ACQ_Variable;
import io.github.binsec.core.acqvariable.CellType;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.learner.ACQ_Query;

public class OverlapConstraint extends ScalarConstraint {

	boolean negated = false;
	int weight = 1;
	ACQ_CellVariable cell1;
	ACQ_CellVariable cell2;
	ACQ_Variable[] vars; // length = 4

	public OverlapConstraint(ACQ_CellVariable cell1, ACQ_CellVariable cell2) {

		super("Overlap", new int[] { cell1.getValue().id, cell1.getSize().id, cell2.getValue().id, cell2.getSize().id },
				new int[] {}, 0);

		cell1.setBigString();
		cell2.setBigString();
		this.cell1 = cell1;
		this.cell2 = cell2;

		ACQ_Variable v1 = cell1.getValue();
		ACQ_Variable v2 = cell1.getSize();
		ACQ_Variable v3 = cell2.getValue();
		ACQ_Variable v4 = cell2.getSize();
		if (v1.getType() != CellType.STR || v3.getType() != CellType.STR) {
			System.err.println("Constraint badly typed");
			System.exit(1);
		} else {
			this.vars = new ACQ_Variable[] { v1, v2, v3, v4 };
		}
	}

	public OverlapConstraint(ACQ_CellVariable cell1, ACQ_CellVariable cell2, boolean negated) {
		this(cell1, cell2);
		if (negated) {
			this.setName("NotOverlap");
			this.negated = negated;
		}
	}

	@Override
	public String getBwConstraint() {
		String val1_value = "v" + this.cell1.getValue().id;
		String val1_size = "v" + this.cell1.getSize().id;
		String val2_value = "v" + this.cell2.getValue().id;
		String val2_size = "v" + this.cell2.getSize().id;
		int n = cell1.getType().getSize(cell1.arch);
		int diff = n - 16;
		String hexcst = "#x" + String.format("%0" + n / 4 + "x", 1);
		String c = String.format(
				"(or (and (bvule %s %s) (bvugt (bvadd %s (bvadd %s ((_ zero_extend %d) %s))) %s)) \n"
						+ "(and (bvule %s %s) (bvugt (bvadd %s (bvadd %s ((_ zero_extend %d) %s))) %s)))",
				val1_value, val2_value, val1_value, hexcst, diff, val1_size, val2_value, val2_value, val1_value,
				val2_value, hexcst, diff, val2_size, val1_value);

		if (!negated)
			return c;
		// "(and " + c + " (= (bvadd " + val1_value + " ((_ zero_extend " + diff + ") "
		// + val1_size
		// + ")) (bvadd " + val2_value + " ((_ zero_extend " + diff + ") " + val2_size +
		// "))))";
		else
			return String.format("(not %s)", c);

	}

	@Override
	public String toBinsecConstraint(ACQ_Query q, Map<String, String> regid) {

		int n = cell1.getType().getSize(cell1.arch) / 4;
		int memsize = cell1.arch.getPtrSizeMemCell() / 4;
		int strlencell1 = q.getValue(cell1.getSize().id).unsigned().intValue();
		int strlencell2 = q.getValue(cell2.getSize().id).unsigned().intValue();

		String toadd = "";
		if (!regid.get("x" + cell1.cellid).isEmpty())
			toadd = "!" + regid.get("x" + cell1.cellid);

		String val1_value = "x" + this.cell1.cellid + toadd;

		toadd = "";
		if (!regid.get("x" + cell2.cellid).isEmpty())
			toadd = "!" + regid.get("x" + cell2.cellid);
		String val2_value = "x" + this.cell2.cellid + toadd;

		String val1_size = "#x" + String.format("%0" + n + "x", strlencell1);

		String val2_size = "#x" + String.format("%0" + n + "x", strlencell2);
		String hexcst = "#x" + String.format("%0" + n + "x", 1);
		String hexcst0 = "#x" + String.format("%0" + cell1.arch.getPtrSizeMemCell() / 4 + "x", 0);

		String c = String.format(
				// "(and (not (= %s %s)) (not (= %s %s))"
				" (or (and (bvule %s %s)                                                                                                                                                                         \n"
						+ "        (bvugt (bvadd %s (bvadd %s %s)) %s)) \n" + "    (and (bvule %s %s) \n"
						+ "        (bvugt (bvadd %s (bvadd %s %s)) %s)))",
				// )",
				// val1_value, hexcst0, val2_value, hexcst0,
				val1_value, val2_value, val1_value, hexcst, val1_size, val2_value, val2_value, val1_value, val2_value,
				hexcst, val2_size, val1_value);

		String val_i;
		if (negated)
			c = String.format("(not %s)", c);

		if (q.getValue(cell1.getValue().id).unsigned().intValue() != 0) {
			c = "(and " + c;
			for (int i = 0; i < strlencell1; i++) {
				toadd = "";
				if (!regid.get("x" + cell1.cellid + "_" + i).isEmpty())
					toadd = "!" + regid.get("x" + cell1.cellid + "_" + i);

				val_i = "x" + this.cell1.cellid + "_" + i + toadd;
				c += String.format(" (not (= %s %s)) ", val_i, hexcst0);
			}
			toadd = "";

			if (!regid.get("x" + cell1.cellid + "_" + strlencell1).isEmpty())
				toadd = "!" + regid.get("x" + cell1.cellid + "_" + strlencell1);
			val_i = "x" + this.cell1.cellid + "_" + strlencell1 + toadd;
			c += String.format(" (= %s %s) )", val_i, hexcst0);
		}
		if (q.getValue(cell2.getValue().id).unsigned().intValue() != 0) {
			c = "(and " + c;
			for (int i = 0; i < strlencell2; i++) {
				toadd = "";
				if (!regid.get("x" + cell2.cellid + "_" + i).isEmpty())
					toadd = "!" + regid.get("x" + cell2.cellid + "_" + i);

				val_i = "x" + this.cell2.cellid + "_" + i + toadd;
				c += String.format(" (not (= %s %s)) ", val_i, hexcst0);
			}
			toadd = "";
			if (!regid.get("x" + cell2.cellid + "_" + strlencell2).isEmpty())
				toadd = "!" + regid.get("x" + cell2.cellid + "_" + strlencell2);
			val_i = "x" + this.cell2.cellid + "_" + strlencell2 + toadd;
			c += String.format(" (= %s %s) )", val_i, hexcst0);
		}

		// System.out.println(c);
		return c;
		// return res;
	}

	public OverlapConstraint(ACQ_CellVariable cell1, ACQ_CellVariable cell2, int weight) {
		this(cell1, cell2);
		this.weight = weight;
	}

	public OverlapConstraint(ACQ_CellVariable cell1, ACQ_CellVariable cell2, boolean negated, int weight) {
		this(cell1, cell2, weight);
		if (negated) {
			this.setName("NotOverlap");
			this.negated = negated;
		}
	}

	@Override
	public ACQ_IConstraint getNegation() {
		return new OverlapConstraint(this.cell1, this.cell2, !this.negated);
	}

	public ACQ_IConstraint getNegation(int weight) {
		return new OverlapConstraint(this.cell1, this.cell2, !this.negated, weight);
	}

	@Override
	public Constraint[] getChocoConstraints(Model model, IntVar... intVars) {
		Constraint cst;

		IntVar var0 = null;
		IntVar var0size = null;
		IntVar var1 = null;
		IntVar var1size = null;

		for (int i = 0; i < intVars.length
				&& (var0 == null || var0size == null || var1 == null || var1size == null); i++) {
			if (intVars[i].getName().equals(vars[0].getName())) {
				var0 = intVars[i];
			} else if (intVars[i].getName().equals(vars[1].getName())) {
				var0size = intVars[i];
			} else if (intVars[i].getName().equals(vars[2].getName())) {
				var1 = intVars[i];
			} else if (intVars[i].getName().equals(vars[3].getName())) {
				var1size = intVars[i];
			}
		}

		var0 = model.intScaleView(var0, 1000);
		var1 = model.intScaleView(var1, 1000);

		if (!negated) {
			BoolVar[] reifyArray = model.boolVarArray(2);
			reifyArray[0] = model.and(model.arithm(var0, "<=", var1), model.arithm(var0, "+", var0size, ">", var1))
					.reify();
			reifyArray[1] = model.and(model.arithm(var1, "<=", var0), model.arithm(var1, "+", var1size, ">", var0))
					.reify();
			cst = model.sum(reifyArray, ">", 0);
		} else {
			BoolVar[] reifyArray1 = model.boolVarArray(2);
			BoolVar[] reifyArray2 = model.boolVarArray(2);

			reifyArray1[0] = model.arithm(var0, ">", var1).reify();
			reifyArray1[1] = model.arithm(var0, "+", var0size, "<=", var1).reify();

			reifyArray2[0] = model.arithm(var1, ">", var0).reify();
			reifyArray2[1] = model.arithm(var1, "+", var1size, "<=", var0).reify();

			cst = model.and(model.sum(reifyArray1, ">", 0), model.sum(reifyArray2, ">", 0));
		}
		return new Constraint[] { cst };
	}

	@Override
	public void toReifiedChoco(Model model, BoolVar b, IntVar... intVars) {

		IntVar var0 = null;
		IntVar var0size = null;
		IntVar var1 = null;
		IntVar var1size = null;

		for (int i = 0; i < intVars.length
				&& (var0 == null || var0size == null || var1 == null || var1size == null); i++) {
			if (intVars[i].getName().equals(vars[0].getName())) {
				var0 = intVars[i];
			} else if (intVars[i].getName().equals(vars[1].getName())) {
				var0size = intVars[i];
			} else if (intVars[i].getName().equals(vars[2].getName())) {
				var1 = intVars[i];
			} else if (intVars[i].getName().equals(vars[3].getName())) {
				var1size = intVars[i];
			}
		}

		var0 = model.intScaleView(var0, 1000);
		var1 = model.intScaleView(var1, 1000);

		if (!negated) {
			BoolVar[] reifyArray = model.boolVarArray(2);
			reifyArray[0] = model.and(model.arithm(var0, "<=", var1), model.arithm(var0, "+", var0size, ">", var1))
					.reify();
			reifyArray[1] = model.and(model.arithm(var1, "<=", var0), model.arithm(var1, "+", var1size, ">", var0))
					.reify();
			model.sum(reifyArray, ">", 0).reifyWith(b);
		} else {
			BoolVar[] reifyArray1 = model.boolVarArray(2);
			BoolVar[] reifyArray2 = model.boolVarArray(2);

			reifyArray1[0] = model.arithm(var0, ">", var1).reify();
			reifyArray1[1] = model.arithm(var0, "+", var0size, "<=", var1).reify();

			reifyArray2[0] = model.arithm(var1, ">", var0).reify();
			reifyArray2[1] = model.arithm(var1, "+", var1size, "<=", var0).reify();

			model.and(model.sum(reifyArray1, ">", 0), model.sum(reifyArray2, ">", 0)).reifyWith(b);
		}

	}

	@Override
	public String getNegName() {
		if (!negated) {
			return "NotOverlap";
		} else {
			return "Overlap";
		}
	}

	@Override
	public String toSmtlib() {
		String o = "(overlap v" + this.cell1.cellid + " v" + this.cell2.cellid + ")";
		if (!negated)
			return o;
		else
			return "(not " + o + ")";
	}

	@Override
	public Bitvec[] getProjection(ACQ_Query query) {
		return new Bitvec[] { query.values[cell1.getValue().id], query.values[cell1.getSize().id],
				query.values[cell2.getValue().id], query.values[cell2.getSize().id] };
	}

	@Override
	public boolean check(ACQ_Query query) {
		Bitvec value[] = this.getProjection(query);
		return check(value);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + cell1.hashCode();
		result = prime * result + cell2.hashCode();

		return result;
	}

	@Override
	public boolean equals(Object obj) {

		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		OverlapConstraint other = (OverlapConstraint) obj;
		if (this.negated != other.negated) {
			return false;
		}
		if (!this.cell1.equals(other.cell1)) {
			return false;
		}
		if (!this.cell2.equals(other.cell2)) {
			return false;
		}

		return true;
	}

	@Override
	public String toString() {
		String val1 = "var" + this.cell1.cellid;
		String val2 = "var" + this.cell2.cellid;
		return getName() + "(" + val1 + ", " + val2 + ")";
	}

	@Override
	public int getWeight() {
		return this.weight;
	}

	@Override
	protected boolean check(Bitvec[] value, int[] coeff) {
		Bitvec v0 = value[0];
		Bitvec v0size = value[1];
		Bitvec v1 = value[2];
		Bitvec v1size = value[3];
		// v0=v0.multiply(new Bitvec(BigInteger.valueOf(1000), v0.size));
		// v1=v1.multiply(new Bitvec(BigInteger.valueOf(1000), v1.size));

		if (!negated) {
			return (v0.ucompareTo(v1) <= 0 && v0.add(v0size).ucompareTo(v1) >= 0)
					|| (v1.ucompareTo(v0) <= 0 && v1.add(v1size).ucompareTo(v0) >= 0);
		} else {
			return (v0.ucompareTo(v1) > 0 || v0.add(v0size).ucompareTo(v1) < 0)
					&& (v1.ucompareTo(v0) > 0 || v1.add(v1size).ucompareTo(v0) < 0);
		}
	}

}
