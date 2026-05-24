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

import java.math.BigInteger;
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

public class IntCellUnaryLTConstraint extends UnaryConstraint {
	ACQ_CellVariable cell1 = null;
	public int constant;
	boolean negated = false;
	ACQ_Variable[] vars;
	int weight = 1;

	public IntCellUnaryLTConstraint(ACQ_CellVariable cell1, int constant) {
		super("LT_" + constant, cell1.getValue().id);

		this.cell1 = cell1;
		this.constant = constant;

		cell1.addValue(constant);
		cell1.addValue(constant + 1);
		cell1.addValue(constant - 1);

		ACQ_Variable v1 = cell1.getValue();
		if (v1.getType() != CellType.INT && v1.getType() != CellType.INT8 && v1.getType() != CellType.UINT && v1.getType() != CellType.UINT8
				&& v1.getType() != CellType.UINT16) {
			System.err.println("Constraint badly typed");
			System.exit(1);
		} else {
			this.vars = new ACQ_Variable[] { v1 };
		}
	}

	public IntCellUnaryLTConstraint(ACQ_CellVariable cell1, int constant, boolean negated) {
		this(cell1, constant);
		if (negated) {
			this.setName("GE_" + constant);
			this.negated = negated;
		}
	}

	public IntCellUnaryLTConstraint(ACQ_CellVariable cell1, int constant, int weight) {
		this(cell1, constant);
		this.weight = weight;
	}

	public IntCellUnaryLTConstraint(ACQ_CellVariable cell1, int constant, boolean negated, int weight) {
		this(cell1, constant, negated);
		this.weight = weight;
	}

	@Override
	public String getBwConstraint() {
		String val1_value = "v" + this.cell1.getValue().id;
		String cst = "#x" + String.format("%0" + cell1.getType().getSize(cell1.arch) / 4 + "x", constant);
		String c;
		if (cell1.getType() == CellType.INT || cell1.getType() == CellType.INT8) {
			c = String.format("(bvslt %s %s)", val1_value, cst);
		} else {
			c = String.format("(bvult %s %s)", val1_value, cst);
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
		String cst = "#x" + String.format("%0" + cell1.getType().getSize(cell1.arch) / 4 + "x", constant);
		String c;
		if (cell1.getType() == CellType.INT || cell1.getType() == CellType.INT8) {
			c = String.format("(bvslt %s %s)", val1_value, cst);
		} else {
			c = String.format("(bvult %s %s)", val1_value, cst);
		}
		if (!negated)
			return c;
		else
			return String.format("(not %s)", c);
	}

	@Override
	public ACQ_IConstraint getNegation() {
		return new IntCellUnaryLTConstraint(this.cell1, this.constant, !this.negated);
	}

	public ACQ_IConstraint getNegation(int weight) {
		return new IntCellUnaryLTConstraint(this.cell1, this.constant, !this.negated, weight);
	}

	@Override
	public Constraint[] getChocoConstraints(Model model, IntVar... intVars) {
		Constraint cst;

		IntVar var0 = null;

		for (int i = 0; i < intVars.length && var0 == null; i++) {
			if (intVars[i].getName().equals(vars[0].getName())) {
				var0 = intVars[i];
			}
		}

		if (!negated) {
			cst = model.arithm(var0, "<", this.constant);
		} else {
			cst = model.arithm(var0, ">=", this.constant);
		}
		return new Constraint[] { cst };
	}

	@Override
	public void toReifiedChoco(Model model, BoolVar b, IntVar... intVars) {

		IntVar var0 = null;

		for (int i = 0; i < intVars.length && var0 == null; i++) {
			if (intVars[i].getName().equals(vars[0].getName())) {
				var0 = intVars[i];
			}
		}

		if (!negated) {
			model.arithm(var0, "<", this.constant).reifyWith(b);
		} else {
			model.arithm(var0, ">=", this.constant).reifyWith(b);
		}

	}

	@Override
	public String getNegName() {
		if (!negated) {
			return "LT_" + this.constant;
		} else {
			return "GE_" + this.constant;
		}
	}

	@Override
	public String toSmtlib() {
		String val1 = "v" + this.cell1.cellid;

		String expr = new String();

		switch (this.cell1.getType()) {
		case INT:
			expr = "(slt " + val1 + " " + String.format("#x%08x", this.constant) + ")";
			break;
		case INT8:
			expr = "(slt " + val1 + " " + String.format("#x%02x", this.constant) + ")";
			break;
		case UINT:
			expr = "(ult " + val1 + " " + String.format("#x%08x", this.constant) + ")";
			break;
		case UINT8:
			expr = "(ult " + val1 + " " + String.format("#x%02x", this.constant) + ")";
			break;
		case UINT16:
			expr = "(ult " + val1 + " " + String.format("#x%04x", this.constant) + ")";
			break;
		default:
			assert false : "not supported type";
			break;
		}
		if (negated)
			return "(not " + expr + ")";

		return expr;

	}

	@Override
	protected boolean check(Bitvec value) {
		Bitvec cst = new Bitvec(BigInteger.valueOf(this.constant), value.size);
		boolean res;
		if ((this.cell1.getType() == CellType.INT)||(this.cell1.getType() == CellType.INT8)) {
			res = value.scompareTo(cst) < 0;
		} else if ((this.cell1.getType().isUnsigned())&&(cell1.getType().isIntKind())) {
			res = value.ucompareTo(cst) < 0;
		} else {
			assert false;
			res = false;
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
		result = prime * result + this.constant;

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
		IntCellUnaryLTConstraint other = (IntCellUnaryLTConstraint) obj;
		if (this.negated != other.negated) {
			return false;
		}

		if (this.constant != other.constant) {
			return false;
		}

		if (!this.cell1.equals(other.cell1)) {
			return false;
		}

		return true;
	}

	@Override
	public String toString() {
		String val1 = "var" + this.cell1.cellid;
		return getName() + "(" + val1 + ", " + this.constant + ")";
	}

	@Override
	public int getWeight() {
		return this.weight;
	}
}
