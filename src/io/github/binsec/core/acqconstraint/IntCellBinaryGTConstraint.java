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

public class IntCellBinaryGTConstraint extends BinaryConstraint {
	boolean negated = false;
	ACQ_CellVariable cell1;
	ACQ_CellVariable cell2;
	ACQ_Variable[] vars; // length = 2

	public IntCellBinaryGTConstraint(ACQ_CellVariable cell1, ACQ_CellVariable cell2) {
		super("GT", cell1.getValue().id, cell2.getValue().id); // TODO : WARNING I don't know if it is good

		this.cell1 = cell1;
		this.cell2 = cell2;

		ACQ_Variable v1 = cell1.getValue();
		ACQ_Variable v2 = cell2.getValue();
		if ((v1.getType() != CellType.INT || v2.getType() != CellType.INT)
				&& (v1.getType() != CellType.INT8 || v2.getType() != CellType.INT8)
				&& (v1.getType() != CellType.UINT || v2.getType() != CellType.UINT)
				&& (v1.getType() != CellType.UINT8 || v2.getType() != CellType.UINT8)
				&& (v1.getType() != CellType.UINT16 || v2.getType() != CellType.UINT16)) {
			System.err.println("Constraint badly typed");
			System.exit(1);
		} else {
			this.vars = new ACQ_Variable[] { v1, v2 };
		}
	}

	public IntCellBinaryGTConstraint(ACQ_CellVariable cell1, ACQ_CellVariable cell2, boolean negated) {
		this(cell1, cell2);
		if (negated) {
			this.setName("LE");
			this.negated = negated;
		}
	}

	@Override
	public String getBwConstraint() {
		String val1_value = "v" + this.cell1.getValue().id;
		String val2_value = "v" + this.cell2.getValue().id;
		String c;
		if (cell1.getType() == CellType.INT|| cell1.getType() == CellType.INT8) {
			c = String.format("(bvsgt %s %s)", val1_value, val2_value);
		} else {
			c = String.format("(bvugt %s %s)", val1_value, val2_value);
		}
		if (!negated)
			return c;
		else
			return String.format("(not %s)", c);
	}

	@Override
	public String toBinsecConstraint(ACQ_Query q, Map<String, String> regid) {

		String toadd = "";
		if (!regid.get("x" + cell1.cellid).isEmpty())
			toadd = "!" + regid.get("x" + cell1.cellid);
		String val1_value = "x" + this.cell1.cellid + toadd;

		toadd = "";
		if (!regid.get("x" + cell2.cellid).isEmpty())
			toadd = "!" + regid.get("x" + cell2.cellid);
		String val2_value = "x" + this.cell2.cellid + toadd;
		String c;
		if (cell1.getType() == CellType.INT || cell1.getType() == CellType.INT8) {
			c = String.format("(bvsgt %s %s)", val1_value, val2_value);
		} else {
			c = String.format("(bvugt %s %s)", val1_value, val2_value);
		}
		if (!negated)
			return c;
		else
			return String.format("(not %s)", c);
	}

	@Override
	public ACQ_IConstraint getNegation() {
		return new IntCellBinaryGTConstraint(this.cell1, this.cell2, !this.negated);
	}

	@Override
	public Constraint[] getChocoConstraints(Model model, IntVar... intVars) {
		Constraint cst;

		IntVar var0 = null;
		IntVar var1 = null;

		for (int i = 0; i < intVars.length && (var0 == null || var1 == null); i++) {
			if (intVars[i].getName().equals(vars[0].getName())) {
				var0 = intVars[i];
			} else if (intVars[i].getName().equals(vars[1].getName())) {
				var1 = intVars[i];
			}
		}

		if (!negated) {
			cst = model.arithm(var0, ">", var1);
		} else {
			cst = model.arithm(var0, "<=", var1);
		}
		return new Constraint[] { cst };
	}

	@Override
	public void toReifiedChoco(Model model, BoolVar b, IntVar... intVars) {

		IntVar var0 = null;
		IntVar var1 = null;

		for (int i = 0; i < intVars.length && (var0 == null || var1 == null); i++) {
			if (intVars[i].getName().equals(vars[0].getName())) {
				var0 = intVars[i];
			} else if (intVars[i].getName().equals(vars[1].getName())) {
				var1 = intVars[i];
			}
		}

		if (!negated) {
			model.arithm(var0, ">", var1).reifyWith(b);
		} else {
			model.arithm(var0, "<=", var1).reifyWith(b);
		}
	}

	@Override
	public String getNegName() {
		if (!negated) {
			return "LT";
		} else {
			return "GE";
		}
	}

	@Override
	public String toSmtlib() {
		String val1 = "v" + this.cell1.cellid;
		String val2 = "v" + this.cell2.cellid;

		if (!negated) {
			if (this.cell1.getType() == CellType.INT || this.cell1.getType() == CellType.INT8) {
				return "(sgt " + val1 + " " + val2 + ")";
			} else if (this.cell1.getType() == CellType.UINT || this.cell1.getType() == CellType.UINT8
					|| this.cell1.getType() == CellType.UINT16) {
				return "(ugt " + val1 + " " + val2 + ")";

			} else {
				assert false;
				return null;
			}
		} else {
			if (this.cell1.getType() == CellType.INT || this.cell1.getType() == CellType.INT8) {
				return "(not (sgt " + val1 + " " + val2 + "))";
			} else if (this.cell1.getType() == CellType.UINT || this.cell1.getType() == CellType.UINT8
					|| this.cell1.getType() == CellType.UINT16) {
				return "(not (ugt " + val1 + " " + val2 + "))";

			} else {
				assert false;
				return null;
			}
		}
	}

	@Override
	protected boolean check(Bitvec value1, Bitvec value2) { // Better if prams could be cells
		boolean res = false;
		if ((this.cell1.getType() == CellType.INT)||(this.cell1.getType() == CellType.INT8)) {
			res = value1.scompareTo(value2) > 0;
		} else if ((this.cell1.getType() == CellType.UINT) || (this.cell1.getType() == CellType.UINT16)
				|| (this.cell1.getType() == CellType.UINT8)) {
			res = value1.ucompareTo(value2) > 0;

		} else {
			assert false;
		}
		if (negated)
			return !res;
		else
			return res;
	}

	@Override
	public boolean check(ACQ_Query query) {
		Bitvec[] value = this.getProjection(query);
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
		IntCellBinaryGTConstraint other = (IntCellBinaryGTConstraint) obj;
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
}
