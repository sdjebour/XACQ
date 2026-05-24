package io.github.binsec.core.acqconstraint;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Map;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;

import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.learner.ACQ_Query;

public class CellLinearConstraint extends ScalarConstraint {

	private final Operator op1;

	// required visibility to allow exportation
	protected String name;
	protected final int cste;
	private final int[] vars;
	private final int[] coeff;
	private String negation;
	ACQ_CellVariable[] cell_list;

	/**
	 * Constructor for a constraint between three variables.
	 * 
	 * @param name  Name of this constraint
	 * @param var   Array of Variables of the constraint
	 * @param coeff Coefficient of the Variables of the constraint
	 * @param op1   Operator 1 of this constraint
	 * @param cste  constant of this constraint
	 * 
	 * @example X + Y -Z < 0
	 */
	
	public CellLinearConstraint(String name,ACQ_CellVariable[] cell_list, int[] coeffs, Operator op,int cste, String negation) {
		super(name, ACQ_CellVariable.cellToIntList(cell_list), coeffs, 0);
		this.name = name;
		this.op1 = op;
		this.cste = cste;
		this.coeff = coeffs;
		this.vars = ACQ_CellVariable.cellToIntList(cell_list);
		this.negation = negation;
		this.cell_list = cell_list;
	}

	@Override 
	public String getName() {
		return this.name + " [ vars :: " + Arrays.toString(vars) + ", coeff=" + Arrays.toString(coeff) + ",  "
				+ op1 + " " + cste + "]";
	}
	
	@Override
	public String getBwConstraint() {
		int bitsize = cell_list[0].getType().getSize(cell_list[0].arch);
		int n = bitsize / 4;
		String res = "(bvadd";
		for (int i = 0; i < variables.length; i++) {
			int var = variables[i];

			int unsigned_coef = (coeff[i] & (int)((1L << bitsize) - 1));
			String coef = "#x" + String.format("%0" + n + "x", unsigned_coef);
			
			res = res + " (bvmul " + coef + " v" + var + ")";
		}
		res = res + ")";
		String hexcste = "#x" + String.format("%0" + n + "x", cste);
		return "(" + Operator.opToSmtlib(op1) + " " + res + " " + hexcste + ")";

	}

	@Override
	public String toBinsecConstraint(ACQ_Query q, Map<String, String> regid) {
		int bitsize = cell_list[0].getType().getSize(cell_list[0].arch);
		int n = bitsize / 4;
		String res = "(bvadd";
		for (int i = 0; i < variables.length; i++) {
			String toadd = "";
			if (!regid.get("x" + cell_list[i].cellid).isEmpty())
				toadd = "!" + regid.get("x" + cell_list[i].cellid);
			String val_value = "x" + this.cell_list[i].cellid + toadd;

			int unsigned_coef = (coeff[i] & (int)((1L << bitsize) - 1));
			String coef = "#x" + String.format("%0" + n + "x", unsigned_coef);

			res = res + " (bvmul " + coef + " " + val_value + ")";
		}
		res = res + ")";
		String hexcste = "#x" + String.format("%0" + n + "x", cste);
		return "(" + Operator.opToSmtlib(op1) + " " + res + " " + hexcste + ")";

	}

	/**
	 * Returns a new CellLinear constraint which is the negation of this constraint
	 * For instance, a constraint with "=" as operator will return a new constraint
	 * with the same variables but with "!=" as operator
	 * 
	 * @return A new CellLinear constraint, negation of this constraint
	 */
	@Override
	public CellLinearConstraint getNegation() {
		return new CellLinearConstraint(this.negation, cell_list, coeff, Operator.getOpposite(op1), cste, getName());
	}

	public String getNegationName() {
		return this.negation;
	}

	/**
	 * Add this constraint to the specified model (a choco solver model in this
	 * case)
	 * 
	 * @param model   Model to add this constraint to
	 * @param intVars Variables of the model involved in this constraint
	 * 
	 */
	@Override
	public Constraint[] getChocoConstraints(Model model, IntVar... intVars) {
		// Deprecated
		return null;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((op1 == null) ? 0 : op1.hashCode());
		for (ACQ_CellVariable cell : cell_list) {
			result = prime * result + cell.hashCode();
		}
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
		CellLinearConstraint other = (CellLinearConstraint) obj;
		if (op1 != other.op1)
			return false;

		if (cste != other.cste)
			return false;

		if (this.getVariables().length != other.getVariables().length)
			return false;

		for (int i = 0; i < this.getVariables().length; i++) {
			if (this.getVariables()[i] != other.getVariables()[i])
				return false;
		}

		for (int i = 0; i < coeff.length; i++) {
			if (coeff[i] != other.coeff[i]) {
				return false;
			}

		}

		return true;
	}

	/**
	 * Add this constraint to the specified model (a choco solver model in this
	 * case)
	 * 
	 * @param model   Model to add this constraint to
	 * @param intVars Variables of the model involved in this constraint
	 * 
	 */
	@Override
	public void toReifiedChoco(Model model, BoolVar b, IntVar... intVars) {
		// Deprecated
	}

	/**
	 * Checks this constraint for a specified set of values
	 * 
	 * @param val1 sum of variable values multiplied by their coefficents which is
	 *             the left side of this constraint
	 * @param cste Value of the second variable of this constraint
	 * @return true if this constraint is satisfied for the specified set of values
	 */
	@Override
	protected boolean check(Bitvec[] vars, int[] coeff) {
		int val = 0;

		for (int i = 0; i < vars.length; i++) {
			val = val + vars[i].signed().intValue() * coeff[i];
		}
		Bitvec val1 = new Bitvec(BigInteger.valueOf(val), vars[0].size);

		Bitvec bvcst = new Bitvec(BigInteger.valueOf(cste), vars[0].size);
		// System.out.println(op1);
		switch (op1) {
		case EQ:
			return val1.equals(bvcst);
		case NQ:
			return !val1.equals(bvcst);
		case SGT:
			return val1.scompareTo(bvcst) > 0;
		case SGE:
			return val1.scompareTo(bvcst) >= 0;
		case SLT:
			return val1.scompareTo(bvcst) < 0;
		case SLE:
			return val1.scompareTo(bvcst) <= 0;
		case UGT:
			return val1.ucompareTo(bvcst) > 0;
		case UGE:
			return val1.ucompareTo(bvcst) >= 0;
		case ULT:
			return val1.ucompareTo(bvcst) < 0;
		case ULE:
			return val1.ucompareTo(bvcst) <= 0;
			
		default:
			assert false;
		}

		return false;
	}

	@Override
	public Bitvec[] getProjection(ACQ_Query query) {

		int index = 0;

		int[] vars = this.getVariables();

		Bitvec[] values = new Bitvec[vars.length];
		for (int numvar : vars)
			values[index++] = query.getValue(numvar);
		return values;
	}
	
	@Override
	public String toString() {
		return this.getName();
	}

	@Override
	public String getNegName() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean check(ACQ_Query query) {
		Bitvec[] value = this.getProjection(query);
		return check(value);
	}

	protected String varToSmtlib(int var) {
		return "v" + var;
	}

	@Override
	public String toSmtlib() {

		String sum = null;
		int bitsize = this.cell_list[0].getType().getSize(cell_list[0].arch);
		int coeff_size=bitsize/4;

		for (int i = 0; i < variables.length; i++) {
			int var = variables[i];
			int coef = coeff[i];
			int unsigned_coef = (coeff[i] & (int)((1L << bitsize) - 1));
			String coefHex = String.format("#x%0"+coeff_size+"x", unsigned_coef);
			String term = "(bvmul " + coefHex + " (value " + varToSmtlib(var) + "))";

			if (sum == null) {
				sum = term;
			} else {
				sum = "(bvadd " + sum + " " + term + ")";
			}
		}

		String csteHex = String.format("#x%0"+coeff_size+"x", cste);

		return "(" + Operator.opToSmtlib(op1) + " " + sum + " " + csteHex + ")";
	}

}
