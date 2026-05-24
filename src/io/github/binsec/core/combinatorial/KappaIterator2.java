package io.github.binsec.core.combinatorial;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqconstraint.ConstraintFactory;
import io.github.binsec.core.acqsolver.ACQ_BitwuzlaSolver;
import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.learner.ACQ_Bias;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.Explanation;
import io.github.binsec.core.tools.ArchType;
import io.github.binsec.core.tools.Chrono;

public class KappaIterator2 implements Iterator<ACQ_IConstraint> {

	protected ACQ_IConstraint next;

	private int addedConst = 0;
	private boolean stop = false;
	private ACQ_BitwuzlaSolver constrSolver;
	private ArchType archtype;
	protected ACQ_CellVariable[] vars;
	protected ACQ_Bias bias;
	protected int checked;
	protected Explanation exp;
	protected ACQ_Query q;
	protected HashSet<ACQ_IConstraint> unsat_list = new HashSet<ACQ_IConstraint>();
	protected ConstraintFactory cf;
	protected int disj_size;
	private Chrono chrono;
	protected boolean solvoptim;
	protected ACQ_Network bk;


	public KappaIterator2(ACQ_BitwuzlaSolver constrSolver, ArchType archtype, ACQ_CellVariable[] vars, ACQ_Bias bias,
			Explanation exp, ACQ_Query q, HashSet<ACQ_IConstraint> unsat_list, ConstraintFactory cf, Chrono chrono,
			boolean solvoptim, ACQ_Network bk) {

		this.constrSolver = constrSolver;
		this.archtype = archtype;
		this.vars = vars;
		this.bias = bias;
		this.exp = exp;
		this.chrono = chrono;
		this.q = q;
		this.unsat_list = unsat_list;
		this.cf = cf;
		// this.checked=this.bias.getSize()-1;
		this.checked = 0;
		this.disj_size = bias.get_Constraint(bias.getSize() - 1).toConstraintSet(cf).size();
		this.solvoptim = solvoptim;
		this.bk = bk;

		advance();
	}

	public ACQ_IConstraint getNext() {
		return next;
	}

	@Override
	public boolean hasNext() {
		return (next != null);
	}

	@Override
	public ACQ_IConstraint next() {
		if (next == null) {
			return null;
		}
		ACQ_IConstraint result = next;
		advance();
		return result;
	}

	private void advance() {
		
		if (checked >= bias.getSize())
			next = null;
		
		while (checked < bias.getSize()) {
			// System.out.println(checked+"/"+bias.getSize());
			ACQ_IConstraint current = bias.get_Constraint(checked);
			// System.out.println(current.toString());

			/*if (current.isDisjunctive()) {
				boolean skip = false;
				// pour chaque contrainte dans unsat_list (include disj)
				if (solvoptim) {

					for (ACQ_IConstraint c : unsat_list) {

						boolean skip_entry = false;
						// pour chaque contrainte dans constraint to check
						// System.out.println(bias.get_Constraint(checked).toString());
						for (ACQ_IConstraint c_ : c.toConstraintSet(cf)) {
							// si il y a une contrainte dans c (de unsat_list) qui n'est pas dans checked =>
							// go to next entry in unsat_list
							if (!current.toConstraintSet(cf).contains(c_)) {
								skip_entry = true;
								break;
							}

							// if we don't break that means we can skip the checked constr
						}
						if (skip_entry)
							continue;
						skip = true;
						break;
						// go next entry in unsat_list

					}
					if (skip) {
						// System.out.println("skipped!");
						//checked++;
						continue;
					}
				}
			}*/
			if (!constInKappaPosExp(current)) {
				unsat_list.add(current);
				checked++;
			} else {
				// System.out.println("exp kappa :" + current.toString());
				next = current;
				checked++;
				break;
			}
			
		}
		
		
		

	}

	private boolean constInKappaPosExp(ACQ_IConstraint c) {
		// if (constrSolver.solve_pos(c.getNegation(), bk, q, archtype)) {
		return constrSolver.solve_check_constraint(q, bk, exp, vars, archtype, c.getNegation(), chrono).isSat();
		// }
		// return true;
	}

}
