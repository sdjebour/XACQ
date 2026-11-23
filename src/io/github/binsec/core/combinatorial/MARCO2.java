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

import static org.mockito.Mockito.RETURNS_DEEP_STUBS;

import java.util.ArrayList;
import java.util.concurrent.TimeoutException;

import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqconstraint.CNF;
import io.github.binsec.core.acqconstraint.Clause;
import io.github.binsec.core.acqconstraint.ConstraintFactory;
import io.github.binsec.core.acqconstraint.ConstraintMapping;
import io.github.binsec.core.acqconstraint.ContradictionSet;
import io.github.binsec.core.acqconstraint.Formula;
import io.github.binsec.core.acqconstraint.Unit;
import io.github.binsec.core.acqconstraint.ConstraintFactory.ConstraintSet;
import io.github.binsec.core.acqsolver.ACQ_ConstraintSolver;
import io.github.binsec.core.acqsolver.SATModel;
import io.github.binsec.core.acqsolver.SATSolver;
import io.github.binsec.core.learner.ACQ_Bias;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.tools.Chrono;

public class MARCO2 extends MSSIter {
	
	protected ACQ_Network basenet;
	protected ACQ_Query next;
	protected ACQ_Network notSeen;
	protected ACQ_Bias bias;
	protected ACQ_Bias known; // known relations
	protected ConstraintMapping mapping;
	protected ACQ_ConstraintSolver solver;
	protected SATSolver satsolver;
	
	protected ArrayList<ACQ_Network> muses = new ArrayList<>();
	
	protected Formula formula;
	
	protected Long timeout;
	protected Long t0;
	
	protected boolean grow2 = true;
	
	public MARCO2(ACQ_Bias bias, ACQ_Network net, 
			ACQ_ConstraintSolver solver, SATSolver satsolver, 
			ConstraintMapping mapping, ContradictionSet backgroundKnowledge, ACQ_Bias known, 
			Long timeout, boolean grow2, Chrono chrono) throws TimeoutException {
		this.timeout = timeout;
		t0 = System.currentTimeMillis();
		this.solver = solver;
		this.satsolver = satsolver;
		this.chrono = chrono;
		this.grow2 = grow2;
		
		this.basenet = net;
		notSeen = new ACQ_Network(net.getFactory(), bias.getVars());
		this.known = known;
		
		this.bias = filterbias(bias, basenet);
		this.mapping = mapping;
		this.formula = new Formula();
		if (backgroundKnowledge != null) this.formula.addCnf(backgroundKnowledge.toCNF());
		
		if (solver.solve(concat(known.getNetwork(), basenet))) {
			chrono.start("gen_query");
			advance();
			chrono.stop("gen_query");
		}
		else next = null;
		
	}
	
	public Formula getFormula() {
		return formula;
	}
	@Override
	public void BlockDownFormula(ACQ_Network ss) {
		formula.addClause(blockDown(ss));
	}
	
	@Override
	public void BlockDownFormula2(ACQ_Network ss) {
		formula.addClause(blockDown2(ss));
	}
	
	public void setMUS(ContradictionSet muses) {
		formula.addCnf(muses.toCNF());
	}
	
	private ACQ_Bias filterbias(ACQ_Bias bias, ACQ_Network net) throws TimeoutException {
		ACQ_Bias res = bias.copy();
		for (ACQ_IConstraint c : bias.getNetwork()) {
			istimeouted(); // throws an exception if timeout reached
			if (net.contains(c)) {
				res.reduce(c);
			}
		}
		return res;
	}
	
	protected boolean istimeouted() throws TimeoutException {
		if (this.timeout != null && 
				(this.timeout <= (System.currentTimeMillis() - t0))) {
			//throw new TimeoutException();
		}
		
		return false;
	}
	
	
	private ACQ_Query solve(ACQ_Network net) {
		return solver.solveQ(concat(basenet, concat(net, known.getNetwork())));
	}
	
	private boolean satisfiable(ACQ_Network net) {
		return !solver.solveQ(concat(basenet, concat(net, known.getNetwork()))).isEmpty();
	}
	
	protected ACQ_Network concat(ACQ_Network net1, ACQ_Network net2) {
		ConstraintFactory fact = bias.getNetwork().getFactory();
		ACQ_Network res = new ACQ_Network(fact, bias.getVars());
		res.addAll(net1, true);
		res.addAll(net2, true);
		return res;
	}
	
	
	public ACQ_Query generate_rand_query_block(ACQ_Scope scp) {
		return solver.solveAnyBlock(scp);
	}
	
	public boolean hasNext() {
		return next != null;
	}
	
	public ACQ_Query next() throws TimeoutException {
	    return next;
	}
	
	@Override
	public void advance() throws TimeoutException {
	    chrono.start("enum_mss");
	    while (true) {
	        istimeouted();
	        SATModel model = satsolver.solve(formula);
	        if (satsolver.isTimeoutReached()) {
	            assert false: "Sat solver timeouted";
	            next = null;
	            return;
	        }

	        if (model != null) {
	            ACQ_Network seed = toNetwork(model);

	            ACQ_Query query = solve(seed);
	            if (!query.isEmpty()) {
	                ACQ_Network mss;
	                if (grow2) {
	                    mss = grow(query, seed, bias);
	                    next = query;
	                }
	                else {
	                    mss = grow(seed, bias);
	                    next = solve(mss);
	                }

	                //formula.addClause(blockDown(mss));
	                break;
	            }
	            else {
	                chrono.start("number_of_muses");
	                ACQ_Network mus = shrink(seed, bias);
	                muses.add(mus);
	                formula.addClause(blockUp(mus));
	                chrono.stop("number_of_muses");
	            }
	        }
	        else {
	            next = null;
	            break;
	        }
	    }
	    chrono.stop("enum_mss");

	}
	
	protected ACQ_Network grow(ACQ_Network seed, ACQ_Bias bias) throws TimeoutException {
		ACQ_Bias diff = bias.copy();
		diff.reduce(seed.getConstraints());
		
		for (ACQ_IConstraint c : diff.getNetwork()) {
			istimeouted();
			ConstraintSet cset = seed.getFactory().createSet(seed.getConstraints());
			cset.add(c);
			ACQ_Network union = new ACQ_Network(seed.getFactory(), cset);
			if (satisfiable(union)) {
				seed.add(c, true);
			}
		}
		
		if (seed.isEmpty()) {
			return null;
		}
		else {
			return seed;
		}
	}
	
	protected ACQ_Network grow(ACQ_Query query, ACQ_Network seed, ACQ_Bias bias) throws TimeoutException {
		ACQ_Bias diff = bias.copy();
		assert seed.check(query);
		
		diff.reduce(seed.getConstraints());
		
		for (ACQ_IConstraint c : diff.getNetwork()) {
			istimeouted();
			
			if (c.check(query)) {
				seed.add(c, true);
			}
		}
		
		if (seed.isEmpty()) {
			return null;
		}
		else {
			return seed;
		}
	}
	
	protected ACQ_Network shrink(ACQ_Network seed, ACQ_Bias C) throws TimeoutException {
		ConstraintFactory fact = bias.getNetwork().getFactory();
		ACQ_Network res = new ACQ_Network(fact, bias.getVars());
		res.addAll(seed, true);
		
		for (ACQ_IConstraint constr : seed) {
			istimeouted();
			ACQ_Network seedminus = new ACQ_Network(fact, bias.getVars());
			seedminus.addAll(res, true);
			seedminus.remove(constr);
			
			if (!satisfiable(seedminus)) {
				res.remove(constr);
			}
			
		}
		
		return res;
	}
	
	private Clause blockDown(ACQ_Network mss) {
		Clause res = new Clause();
		for (ACQ_IConstraint constr : bias.getNetwork()) {
			if (!mss.contains(constr)) {
				res.add(mapping.get(constr));
			}
		}
		return res;
	}
	
	private Clause blockDown2(ACQ_Network mss) {
		Clause res = new Clause();
		for (ACQ_IConstraint constr : mss) {
				res.add(mapping.get(constr.getNegation()));
		}
		return res;
	}
	
	private Clause blockUp(ACQ_Network mss) {
		Clause res = new Clause();
		for (ACQ_IConstraint constr : mss) {
			Unit u = mapping.get(constr).clone();
			u.setNeg();
			res.add(u);
		}
		return res;
	}
	
	protected ACQ_Network toNetwork(SATModel model) {
		//chrono.start("to_network");
		assert(model != null);
		ACQ_Network network = new ACQ_Network(bias.getNetwork().getFactory(), bias.getVars());
		
		for (ACQ_IConstraint constr : model.getPositive()) {
			assert constr != null;
			network.add(constr, true);
		}
		
		//chrono.stop("to_network");
		return network;
	}
	
	public ArrayList<ACQ_Network> getMuses() {
		return muses;
	}
	
	@Override
	public ACQ_Network queryToMss(ACQ_Query query) {
		//get the mss for the query
		ConstraintFactory fact = bias.getNetwork().getFactory();
		ConstraintSet set = fact.createSet();
		for (ACQ_IConstraint c : bias.getConstraints()) {
			if (c.check(query)) {
				set.add(c);
			}
		}
		return new ACQ_Network(fact,set);
	}
	
	@Override
	public void unitPropagation(ACQ_Network ss) {
		for(CNF cnf : formula.copy().getCnfs()) {
			for(Clause cl : cnf) {
				if(cl.containsAll(ss)) {
					formula.getCnfs().remove(cl);
				}
			}
		}
		
	}
	
	public boolean already_processed(ACQ_Network mss) {
		
	return formula.contains_subset(blockDown2(mss));
		
	}
	
}
