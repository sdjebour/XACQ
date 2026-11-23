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

package io.github.binsec.core.combinatorial;

import java.util.ArrayList;
import java.util.concurrent.TimeoutException;

import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqconstraint.ContradictionSet;
import io.github.binsec.core.acqsolver.ACQ_BitwuzlaSolver;
import io.github.binsec.core.learner.ACQ_Bias;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.learner.Explanation;
import io.github.binsec.core.tools.ArchType;
import io.github.binsec.core.tools.Chrono;

public class MSSEnumIter {
	
	protected Chrono chrono = null;
	Explanation exp = null;
	ACQ_BitwuzlaSolver solver = null;
	ACQ_Query next;
	String mss_block = "";
	ArchType archtype;
	
	public MSSEnumIter(Explanation exp, ACQ_BitwuzlaSolver solver, ArchType archtype, Chrono chrono) {
		this.chrono= chrono;
		this.solver=solver;
		this.exp=exp;
		this.archtype=archtype;
	}
	
	
	public boolean hasNext() {
		return next!=null;
	}
	
	public ACQ_Query next() {
		return next;
	}
	
	
	
	public void setChrono(Chrono chrono) {
		this.chrono = chrono;	
	}

	protected boolean istimeouted(Long learningtimeout, Long t0) throws TimeoutException {
		if (learningtimeout != null && 
				(learningtimeout <= (System.currentTimeMillis() - t0))) {
			throw new TimeoutException();
		}
		
		return false;
	}
	
	public void advance(ACQ_Bias bias, ACQ_Query q, ACQ_Network bk, Long learningtimeout, Long t0) throws TimeoutException {
		istimeouted(learningtimeout, t0);
		next = solver.solveEnum(exp, mss_block, q, archtype, bk);
		if(next!=null) {
			mss_block=mss_block + block(next,bias);
		}
	}

	public String block(ACQ_Query q, ACQ_Bias bias) {
		//System.out.println(""+q.toString2());
		ACQ_Network mss_q=q.tomss(bias);
		String toadd="(assert (not (and ";
		for (ACQ_IConstraint c : mss_q) {
			
				 toadd=toadd+" "+c.toBinsecConstraint(q, exp.getRegId());
		}
			  toadd = toadd+")))\n";
			  
		return toadd;
	}

	
}
