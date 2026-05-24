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

import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.tools.Chrono;

public class ContradictionSet {
	CNF cnf;
	ConstraintFactory factory;
	ACQ_Scope scope;
	ConstraintMapping mapping;

	public ContradictionSet(ConstraintFactory factory, ACQ_Scope scope, ConstraintMapping mapping) {
		this.cnf = new CNF();
		this.factory = factory;
		this.scope = scope;
		this.mapping = mapping;
	}

	public CNF toCNF() {
		return cnf;
	}

	public int getSize() {
		return cnf.size();
	}

	public void unitPropagate(Unit unit, Chrono chrono) {
		cnf.unitPropagate(unit, chrono);
	}

	public void add(Contradiction contr) {
		cnf.add(contr.toClause(mapping));
	}

	public void addFact(Contradiction contr) {
		cnf.add(contr.toFact(mapping));
	}

	public String toString() {
		return this.toCNF().toString();
	}

	public boolean contains(Contradiction contr) {
		return cnf.contains(contr.toClause(mapping));
	}

	public ACQ_Network toNetwork(ACQ_Network bias) {
		ACQ_Network bk = new ACQ_Network(factory, scope);
		for (Clause cl : cnf) {
			if (cl.getSize() == 1) {
				bk.add(cl.get(0).getConstraint(), true);
			} else {
				ACQ_DisjunctionConstraint clDisjConstr = new ACQ_DisjunctionConstraint(factory,
						cl.toNetwork(factory, scope).getConstraints());
				bk.add(clDisjConstr, true);
			}
		}
		return bk;
	}

}
