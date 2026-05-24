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

package io.github.binsec.core;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.TimeoutException;

import io.github.binsec.core.acqconstraint.ACQ_ConjunctionConstraint;
import io.github.binsec.core.acqconstraint.ACQ_DisjunctionConstraint;
import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqconstraint.CNF;
import io.github.binsec.core.acqconstraint.Clause;
import io.github.binsec.core.acqconstraint.ConstraintFactory;
import io.github.binsec.core.acqconstraint.ConstraintFactory.ConstraintSet;
import io.github.binsec.core.acqconstraint.ConstraintMapping;
import io.github.binsec.core.acqconstraint.Contradiction;
import io.github.binsec.core.acqconstraint.ContradictionSet;
import io.github.binsec.core.acqconstraint.Formula;
import io.github.binsec.core.acqconstraint.Unit;
import io.github.binsec.core.acqsolver.ACQ_BitwuzlaSolver;
import io.github.binsec.core.acqsolver.ACQ_ConstraintSolver;
import io.github.binsec.core.acqsolver.ACQ_IDomain;
import io.github.binsec.core.acqsolver.SATModel;
import io.github.binsec.core.acqsolver.SATSolver;
import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.combinatorial.KappaIterator;
import io.github.binsec.core.combinatorial.KappaIterator2;
import io.github.binsec.core.learner.ACQ_Bias;
import io.github.binsec.core.learner.ACQ_Learner;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.Answer;
import io.github.binsec.core.learner.Explanation;
import io.github.binsec.core.tools.ArchType;
import io.github.binsec.core.tools.Chrono;
import io.github.binsec.core.tools.QueryPrinter;
import io.github.binsec.core.tools.TimeUnit;

public class ACQ_ECONACQ {
	protected ACQ_Bias bias;
	protected ACQ_Bias bias_minus;

	protected ACQ_Learner learner;
	protected ACQ_BitwuzlaSolver constrSolver;
	protected ACQ_IDomain domain;
	protected CNF T;
	protected boolean verbose = false;
	protected ConstraintMapping mapping;
	protected SATSolver satSolver;
	protected ConstraintFactory constraintFactory;
	protected ACQ_Network learned_network;
	protected ACQ_Bias knownconstraints = null;
	protected ArrayList<ACQ_Network> strategy = null;
	protected ContradictionSet backgroundKnowledge = null;
	protected Chrono chrono;
	protected Long learningtimeout;
	protected Long t0;
	public boolean timeouted = false;
	protected ArrayList<ACQ_Query> asked = new ArrayList<>();
	protected ArrayList<String> asked_debug = new ArrayList<>();
	protected ArrayList<ACQ_Query> preprocanswered = new ArrayList<>();
	protected ACQ_CellVariable[] vars;
	protected boolean active = true;
	protected boolean weighted = false;
	protected ACQ_Query collapsingQuery;
	protected QueryPrinter qp;
	private ArchType archtype;
	private int nbrQueries;
	private boolean bias_optim=false;
	private int nbquery = 0;
	private int strong_inf_query = 0;
	private ArrayList<Double> solvtimeperQuery_sum = new ArrayList<>();
	private ArrayList<ArrayList<Double>> solvtimeperQuery = new ArrayList<>();
	// private ArrayList<Explanation> listnegexp = new ArrayList<Explanation>();
	private int strong_inf_query2 = 0;
	private boolean solvoptim;

	public ACQ_ECONACQ(ACQ_Learner learner, ACQ_Bias bias, SATSolver sat, ACQ_ConstraintSolver solv) {
		this.bias = bias;
		this.constraintFactory = bias.network.getFactory();
		this.learner = learner;
		this.satSolver = sat;
		this.constrSolver = (ACQ_BitwuzlaSolver) solv;
		this.domain = solv.getDomain();
		this.mapping = new ConstraintMapping();

		for (ACQ_IConstraint c : bias.getConstraints()) {
			String newvarname = c.getName() + c.getVariables();
			Unit unit = this.satSolver.addVar(c, newvarname);
			this.mapping.add(c, unit);

			ACQ_IConstraint neg = c.getNegation();
			if (!bias.contains(neg)) {
				newvarname = neg.getName() + neg.getVariables();
				unit = this.satSolver.addVar(neg, newvarname);
				this.mapping.add(neg, unit);
			}
		}
		assert mapping.size() >= bias.getSize() : "mapping must contain more elements than bias";
		filter_conjunctions();
		this.bias_minus = bias.copy();

	}

	public ACQ_ECONACQ(ACQ_Learner learner, ACQ_Bias bias, ACQ_Bias known, SATSolver sat, ACQ_ConstraintSolver solv,
			ArchType archtype, int nbrQueries, boolean solvoptim, boolean bias_optim) {
		this.bias = bias;
		bias_optim= this.bias_optim;
		this.knownconstraints = known;
		this.constraintFactory = bias.network.getFactory();
		this.learner = learner;
		this.satSolver = sat;
		this.constrSolver = (ACQ_BitwuzlaSolver) solv;
		this.domain = solv.getDomain();
		this.mapping = new ConstraintMapping();
		this.archtype = archtype;
		this.nbrQueries = nbrQueries;
		this.solvoptim = solvoptim;

		for (ACQ_IConstraint c : bias.getConstraints()) {
			String newvarname = c.getName() + c.getVariables();
			Unit unit = this.satSolver.addVar(c, newvarname);
			this.mapping.add(c, unit);

			ACQ_IConstraint neg = c.getNegation();
			if (!bias.contains(neg)) {
				newvarname = neg.getName() + neg.getVariables();
				unit = this.satSolver.addVar(neg, newvarname);
				this.mapping.add(neg, unit);
			}
		}

		for (ACQ_IConstraint c : knownconstraints.getConstraints()) {
			if (!bias.contains(c)) {
				String newvarname = c.getName() + c.getVariables();
				Unit unit = this.satSolver.addVar(c, newvarname);
				this.mapping.add(c, unit);
			}

			ACQ_IConstraint neg = c.getNegation();
			if (!bias.contains(neg)) {
				String newvarname = neg.getName() + neg.getVariables();
				Unit unit = this.satSolver.addVar(neg, newvarname);
				this.mapping.add(neg, unit);
			}
		}

		assert mapping.size() >= bias.getSize() : "mapping must contain more elements than bias";
		filter_conjunctions();
		this.bias_minus = bias.copy();

	}

	public void setQueryPrinter(QueryPrinter qp) {
		this.qp = qp;
	}

	public void setWeighted(boolean b) {
		weighted = b;
	}

	protected void filter_conjunctions() {
		for (Unit unit : mapping.values()) {
			ACQ_IConstraint c = unit.getConstraint();
			if (c instanceof ACQ_ConjunctionConstraint) {
				bias.reduce(c);
			}
		}
	}

	public void setCellVariables(ACQ_CellVariable[] list) {
		vars = list;
	}

	public void setPreprocAnswered(ArrayList<ACQ_Query> list) {
		this.preprocanswered = list;
	}

	public void setPassive() {
		this.active = false;
	}

	public void setLearningTimeout(Long tm) {
		this.learningtimeout = tm;
	}

	public void setStrat(ArrayList<ACQ_Network> strat) {
		this.strategy = strat;
	}

	public void setChrono(Chrono chrono) {
		this.chrono = chrono;
	}

	public void setBackgroundKnowledge(ContradictionSet back) {
		this.backgroundKnowledge = back;
	}

	public ContradictionSet getBackgroundKnowledge() {
		return this.backgroundKnowledge;
	}

	public ArrayList<ACQ_Query> getAskedQueries() {
		return this.asked;
	}

	public ArrayList<ACQ_Query> getAskedQueriesPos() {
		ArrayList<ACQ_Query> pos = new ArrayList<>();
		for (ACQ_Query e : asked) {
			if (e.isPositive()) {
				pos.add(e);
			}
		}
		return pos;
	}

	public ArrayList<ACQ_Query> getAskedQueriesNeg() {
		ArrayList<ACQ_Query> neg = new ArrayList<>();
		for (ACQ_Query e : asked) {
			if (e.isNegative()) {
				neg.add(e);
			}
		}
		return neg;
	}

	public ACQ_Bias getBias() {
		return bias;
	}

	public ACQ_Network getLearnedNetwork() {
		return learned_network;
	}

	public ACQ_Query getCollapsingQuery() {
		if (collapsingQuery == null)
			collapsingQuery = T.getInconsistency();
		assert collapsingQuery.isNegative();
		return collapsingQuery;
	}

	public void setVerbose(boolean verbose) {

		this.verbose = verbose;
	}

	protected boolean istimeouted() throws TimeoutException {
		if (this.learningtimeout != null && (this.learningtimeout <= (System.currentTimeMillis() - this.t0))) {
			throw new TimeoutException();
		}

		return false;
	}

	protected boolean istimeouted_nothrow() {
		try {
			istimeouted();
			return false;
		} catch (TimeoutException e) {
			return true;
		}
	}

	public ACQ_Query query_gen(CNF T, ContradictionSet N) throws Exception {
		ACQ_Query q = new ACQ_Query();
		Clause alpha = new Clause();
		int epsilon = 0;
		int t = 0;
		boolean skip_buildformula = false;
		Formula form = null;
		Boolean splittable = null;
		while (!istimeouted() && q.isEmpty() && !T.isMonomial()) {
			if (!skip_buildformula) {
				Clause newalpha;

				if (alpha.isEmpty() && !(newalpha = T.getUnmarkedNonUnaryClause()).isEmpty()) {
					alpha = newalpha;
					epsilon = 0;
					t = 1; // Optimal in expectation
					// t = Math.max(alpha.getSize() -1, 1); // Optimistic
				}
				splittable = (!alpha.isEmpty() && ((t + epsilon < alpha.getSize()) || (t - epsilon > 0)));
				chrono.start("build_formula");
				// form = BuildFormula(splittable, T, N, filteralpha(alpha), t, epsilon);
				form = BuildFormula(splittable, T, N, alpha, t, epsilon);
				chrono.stop("build_formula");
				assert (form != null);
				form.addCnf(N.toCNF());
			}
			skip_buildformula = false;
			SATModel model = satSolver.solve(form);
			if (satSolver.isTimeoutReached()) {
				assert (q.isEmpty());
				return q; // Collapse
			}

			if (model == null) {
				assert !alpha.isEmpty() : "invariant: alpha should not be empty";

				if (splittable) {
					epsilon += 1;
				} else {
					T.remove(alpha);
					for (Unit unit : alpha) {
						assert !unit.isNeg() : "literals in alpha should not be negated";
						chrono.stop("first_constr_learned");
						Clause fromalpha = new Clause(unit);
						fromalpha.setOriginQuery(alpha.getOriginQuery());
						T.add(fromalpha);
						T.unitPropagate(unit, chrono);
						bias_minus.reduce(unit.getConstraint().getNegation());
					}
					alpha = new Clause(); // Empty clause
					assert alpha.isEmpty() : "The empty clause should be empty";
				}
			} else {
				ACQ_Network network = toNetwork(model);
				q = constrSolver.solveQ(network);

				if (constrSolver.isTimeoutReached()) {
					assert q.isEmpty() : "Timeout reached but q is not empty";
					return q;
				}

				if (q.isEmpty()) {
					network = filternet(network);
					Contradiction unsatCore = quickExplain(
							new ACQ_Network(constraintFactory, bias.network.getVariables()), network);
					assert (unsatCore != null && !unsatCore.isEmpty());
					N.add(unsatCore);
					/*
					 * if (!alpha.isEmpty()) { // Here splittalbe, alpha (!= empty) and T does not
					 * change (only N change) // so BuildFormula will return the same formula
					 * skip_buildformula = true; // Here splittalbe, alpha (!= empty) and T does not
					 * change (only N change) so BuildFormula }
					 */
				} else {
					if (!splittable && !alpha.isEmpty())
						alpha.mark();
				}

			}

		}
		if (q.isEmpty())
			q = irredundantQuery(T);
		return q;
	}

	protected ACQ_Network filternet(ACQ_Network net) {
		ACQ_Network res = new ACQ_Network(constraintFactory, bias.getVars());
		for (ACQ_IConstraint constr : net) {
			boolean toadd = true;

			if (constr instanceof ACQ_DisjunctionConstraint) {
				ACQ_DisjunctionConstraint disj = (ACQ_DisjunctionConstraint) constr;
				for (ACQ_IConstraint added : res) {
					if (disj.contains(added)) {
						toadd = false;
						break;
					}
				}
			}

			if (constr instanceof ACQ_ConjunctionConstraint) {
				ACQ_ConjunctionConstraint conj = (ACQ_ConjunctionConstraint) constr;
				boolean included = true;
				for (ACQ_IConstraint subconj : conj.getConstraints()) {
					if (!res.contains(subconj)) {
						included = false;
						break;
					}
				}

				toadd = !included;
			}

			if (toadd) {
				res.add(constr, true);
			}
		}
		return res;
	}

	protected Formula BuildFormula(Boolean splittable, CNF T, ContradictionSet N, Clause alpha, int t, int epsilon)
			throws TimeoutException {
		Formula res = new Formula();
		if (!alpha.isEmpty()) {
			res.addCnf(T);
			// No need to remove unary negative as it is never added to T
			for (ACQ_IConstraint c : bias_minus.getConstraints()) {
				istimeouted();
				// No need to check if T contains unary negative as it is never added to T
				boolean cont = alpha.contains(c);
				if (splittable && !cont && !alpha.contains(c.getNegation())) {
					res.addClause(new Clause(mapping.get(c)));
				}
				if (cont) {
					Clause newcl = new Clause();
					newcl.add(mapping.get(c));
					newcl.add(mapping.get(c.getNegation()));
					res.addClause(newcl);
					if (weighted)
						res.addMinimization(newcl);
				}
			}

			int lower, upper;
			if (splittable && !weighted) {
				lower = Math.max(alpha.getSize() - t - epsilon, 1);
				upper = Math.min(alpha.getSize() - t + epsilon, alpha.getSize() - 1);
			} else {
				lower = 1;
				upper = alpha.getSize() - 1;
			}

			res.setAtLeastAtMost(alpha, lower, upper); // atLeast and atMost are left symbolic in order to let the
														// solver encode it at will
		} else {
			CNF F = T.clone();
			Clause toadd = new Clause();
			// All constraints not in bias_minus are set to false
			for (ACQ_IConstraint constr : bias_minus.getConstraints()) {
				istimeouted();
				if (isUnset(constr, T, N)) {
					// constr is unset
					Unit toremove = mapping.get(constr.getNegation()).clone();
					toremove.setNeg();

					F.removeIfExists(new Clause(toremove)); // TODO check if can be removed
					// F.remove(new Clause(toremove));

					toadd.add(mapping.get(constr.getNegation()));
				}
			}

			assert !toadd.isEmpty() : "toadd should not be empty";
			F.add(toadd);
			res.addCnf(F);
		}
		return res;
	}

	protected boolean isUnset(ACQ_IConstraint constr, CNF T, ContradictionSet N) {
		Unit unit = mapping.get(constr);
		Unit neg = unit.clone();
		neg.setNeg();

		CNF tmp1 = T.clone();
		tmp1.concat(N.toCNF());
		CNF tmp2 = tmp1.clone();

		tmp1.add(new Clause(unit));
		tmp2.add(new Clause(neg));

		return satSolver.solve(tmp1) != null && satSolver.solve(tmp2) != null;
	}

	protected ACQ_Query irredundantQuery(CNF T) {
		//int i=0;
		assert (T.isMonomial());
		ACQ_Network learned = new ACQ_Network(constraintFactory, bias.getVars(),
				constraintFactory.createSet(T.getMonomialPositive()));
		learned.addAll(knownconstraints.getNetwork(), true);
		long startTime = System.currentTimeMillis();
		while (System.currentTimeMillis() - startTime < 100) { // Until 0.1 second timeout
			ACQ_Query q = constrSolver.solveQ(learned);

			ConstraintSet kappa = bias_minus.getKappa(q);
			for (Clause clause : T) { // TODO check if we cannot remove the loop
				Unit unit = clause.get(0);
				if (unit.isNeg())
					kappa.remove(unit.getConstraint());
			}

			if (kappa.size() > 0) {
				return q;
			}
		}

		for (ACQ_IConstraint c : bias_minus.getConstraints()) {
			if (!learned.contains(c)) {
				learned.add(c.getNegation(), true);

				ACQ_Query q = constrSolver.solveQ(learned);
				learned.remove(c.getNegation());
				if (!q.isEmpty())
					return q;
				else {
					T.add(new Clause(mapping.get(c)));
					// Here I do not add a originQuery as another clause is redundant
				}
			}
		}
		return new ACQ_Query();
	}

	protected Contradiction quickExplain(ACQ_Network b, ACQ_Network network) {
		chrono.start("quick_explain");
		Contradiction result;
		if (network.size() == 0) {
			result = new Contradiction(new ACQ_Network());
		} else {
			ACQ_Network res = quick(b, b, network);
			assert !isConsistent(res) : "quickExplain must returned inconsistent networks";
			result = new Contradiction(res);
		}
		chrono.stop("quick_explain");
		return result;
	}

	protected ACQ_Network quick(ACQ_Network b, ACQ_Network delta, ACQ_Network c) {
		if (delta.size() != 0 && !isConsistent(b)) {
			return new ACQ_Network(c.getFactory(), c.getFactory().createSet());
		}
		if (c.size() == 1)
			return c;

		ACQ_Network c1 = new ACQ_Network(constraintFactory, bias.network.getVariables());
		ACQ_Network c2 = new ACQ_Network(constraintFactory, bias.network.getVariables());

		int i = 0;
		for (ACQ_IConstraint constr : c.getConstraints()) {
			if (i < c.size() / 2) {
				c1.add(constr, true);
			} else {
				c2.add(constr, true);
			}
			i += 1;
		}

		ACQ_Network b_union_c1 = new ACQ_Network(constraintFactory, b, bias.network.getVariables());
		b_union_c1.addAll(c1, true);
		ACQ_Network delta2 = quick(b_union_c1, c1, c2);

		ACQ_Network b_union_delta2 = new ACQ_Network(constraintFactory, b, bias.network.getVariables());
		b_union_delta2.addAll(delta2, true);
		ACQ_Network delta1 = quick(b_union_delta2, delta2, c1);

		delta1.addAll(delta2, true);
		return delta1;
	}

	protected Boolean isConsistent(ACQ_Network network) {
		return constrSolver.solve(network);
	}

	protected ACQ_Query preproc_query_gen() {
		if (this.strategy != null && this.strategy.size() > 0) {
			ACQ_Network s = this.strategy.get(0);
			this.strategy.remove(0);
			s.addAll(knownconstraints.getNetwork(), true);
			return constrSolver.solveQ(s);
		} else {
			return new ACQ_Query();
		}
	}

	

	// this is for non implication
	private boolean skip_notimp_v2(ACQ_IConstraint cl, HashSet<ACQ_IConstraint> notImp_list) {
		for (ACQ_IConstraint c : cl.toConstraintSet(constraintFactory)) {
			if (notImp_list.contains(c)) {
				return true;
			}
		}
		return false;
	}

// this is for implication
	private boolean skip_imp_or_deduced(ACQ_IConstraint c, HashSet<ACQ_IConstraint> imp_list) {
		for (ACQ_IConstraint c_ : c.toConstraintSet(constraintFactory)) {
			if (imp_list.contains(c_))
				return true;
		}
		return false;
	}
	
	private boolean skip_notimp(ACQ_IConstraint cl, HashSet<ACQ_IConstraint> notImp_list) {
		for (ACQ_IConstraint c : cl.toConstraintSet(constraintFactory)) {
			if (notImp_list.contains(c)) {
				return true;
			}
		}
		return false;
	}

	private boolean skip_imp(ACQ_IConstraint c, HashSet<ACQ_IConstraint> imp_list) {
		for (ACQ_IConstraint c_ : c.toConstraintSet(constraintFactory)) {
			if (!imp_list.contains(c_))
				return false;
		}
		return true;
	}



	private int generelize_simple_learned(Explanation negexp, ACQ_Query q) {

		int dsize = 0;
		int res=0;
		HashSet<ACQ_IConstraint> imp_list = new HashSet<ACQ_IConstraint>();
		HashSet<ACQ_IConstraint> notImp_list = new HashSet<ACQ_IConstraint>();
		int added = 0;
		ACQ_Network learned = new ACQ_Network(constraintFactory, bias.getVars());
		ACQ_Network bias_copy=bias_minus.copy().getNetwork();
		// CHANGE :for (ACQ_IConstraint c : bias_minus.copy().getNetwork()) {
		for (ACQ_IConstraint c : bias_minus.copy().getNetwork()) {
			//if (!learned.getLearnedNetwork(T).contains(c)) {
				assert dsize <= c.toConstraintSet(constraintFactory).size();
				dsize = c.toConstraintSet(constraintFactory).size();
				if (solvoptim) {

					if (skip_imp(c.getNegation(), imp_list)) {
						res++;
						updateClausalTheory(c);
						continue;
					}
					
				}



					boolean stop=false;
					for(ACQ_IConstraint c_:imp_list) {
						if(c_.isSubsumed(c, constraintFactory)) {
							res++;
							updateClausalTheory(c);
							stop=true;
							break;
						}
					}
					if(stop) continue;
					
					if (constrSolver.solve(c.getNegation(), q, knownconstraints.network, learned, archtype, chrono)) {
	
						if (!constrSolver.solveGen(c.getNegation(), learned, knownconstraints.network, negexp, archtype,
								chrono, q)) {
							res++;
							updateClausalTheory(c);
							//if (solvoptim)
							imp_list.add(c);
						} 
						else if (solvoptim) {
							notImp_list.add(c.getNegation());
						}
	
					}
				//}
				//else {
				//	updateClausalTheory(c);
				//	added++;
				//}
			//}
		}

		return res;
	}
	
	private int generelize_simple_learned2(Explanation negexp, ACQ_Query q) {

		int dsize = 0;
		int res=0;
		HashSet<ACQ_IConstraint> imp_list = new HashSet<ACQ_IConstraint>();
		HashSet<ACQ_IConstraint> notImp_list = new HashSet<ACQ_IConstraint>();
		int added = 0;
		ACQ_Network learned = new ACQ_Network(constraintFactory, bias.getVars());
		ACQ_Network bias_copy=bias.copy().getNetwork();
		// CHANGE :for (ACQ_IConstraint c : bias_minus.copy().getNetwork()) {
		for (ACQ_IConstraint c : bias.copy().getNetwork()) {
			//if (!learned.getLearnedNetwork(T).contains(c)) {
				assert dsize <= c.toConstraintSet(constraintFactory).size();
				dsize = c.toConstraintSet(constraintFactory).size();
				if (solvoptim) {

					if (skip_imp(c.getNegation(), imp_list)) {
						res++;
						updateClausalTheory(c);
						continue;
					}
					
				}



					boolean stop=false;
					for(ACQ_IConstraint c_:imp_list) {
						if(c_.isSubsumed(c, constraintFactory)) {
							res++;
							updateClausalTheory(c);
							stop=true;
							break;
						}
					}
					if(stop) continue;
					
					if (constrSolver.solve(c.getNegation(), q, knownconstraints.network, learned, archtype, chrono)) {
	
						if (!constrSolver.solveGen(c.getNegation(), learned, knownconstraints.network, negexp, archtype,
								chrono, q)) {
							res++;
							updateClausalTheory(c);
							//if (solvoptim)
							imp_list.add(c);
						} 
						else if (solvoptim) {
							notImp_list.add(c.getNegation());
						}
	
					}
				//}
				//else {
				//	updateClausalTheory(c);
				//	added++;
				//}
			//}
		}

		return res;
	}


	private int updateClausalTheory(ACQ_IConstraint c) {
		int res=1;
		//System.out.println("to add: " + c.toString());
		Unit unit;
		unit = mapping.get(c).clone();
		T.unitPropagate(unit, chrono);
		Clause unary = new Clause(unit);
		T.add(unary);

		// Remove it
		if(bias_minus.contains(c.getNegation())) {
			bias_minus.reduce(c.getNegation());
			unit = mapping.get(c.getNegation()).clone();
			unit.setNeg();
			T.unitPropagate(unit, chrono);
			//res++;
		}
		
		return res;
	}

	public boolean process() throws Exception {
		chrono.start("ct_found");
		this.t0 = System.currentTimeMillis();
		boolean convergence = false;
		boolean collapse = false;

		T = new CNF();
		ContradictionSet N;
		if (this.backgroundKnowledge == null) {
			N = new ContradictionSet(constraintFactory, bias.network.getVariables(), mapping);
		} else {
			N = this.backgroundKnowledge;
		}

		chrono.start("total_acq_time");
		chrono.start("first_constr_learned");
		//collapse = preprocess(T, N);

		while (active && !(collapse || convergence)) {

			if (istimeouted_nothrow()) {
				this.timeouted = true;
				break;
			}

			if (bias_minus.getConstraints().isEmpty())
				break;

			ACQ_Query membership_query;
			try {
				chrono.start("gen_query");
				membership_query = query_gen(T, N);
				chrono.stop("gen_query");
			} catch (TimeoutException e) {
				this.timeouted = true;
				chrono.stop("gen_query");
				break;
			}
			assert membership_query != null : "membership query can't be null";

			if (constrSolver.isTimeoutReached() || satSolver.isTimeoutReached()) {
				collapse = true;
				break;
			}

			if (membership_query.isEmpty()) {
				convergence = true;
			} else {
				if (verbose)
					System.out.print(nbquery + ") " + qp.toString(membership_query));
				Explanation exp = new Explanation();
				ACQ_Network learned = new ACQ_Network(constraintFactory, bias.getVars());
				learned.getLearnedNetwork(T);
				int old_size=bias_minus.getSize()-learned.size();
				chrono.start("oracle_time");
				Answer answer = learner.ask(membership_query, exp);
				chrono.stop("oracle_time");
				if (verbose)
					System.out.println("::" + membership_query.getClassification().toString());
				asked.add(membership_query);
				assert !asked_debug.contains(membership_query.toString());
				asked_debug.add(membership_query.toString());
				ConstraintSet kappa = bias_minus.getKappa(membership_query);
				ConstraintSet kappa2 = bias.getKappa(membership_query);

				// System.out.println(kappa.toString2());

				int s = kappa.size();
				if (answer == Answer.YES) {
					int kappaexp_size = 0;
					HashSet<ACQ_IConstraint> network = new HashSet<ACQ_IConstraint>();
					chrono.start("explanation_solver_time_pos_query");
					if(bias_optim) {
						
					KappaIterator iter = new KappaIterator(constrSolver, archtype, vars, bias_minus, exp,
							membership_query, network, constraintFactory, chrono, solvoptim, knownconstraints.network);
					while (iter.hasNext()) {
						ACQ_IConstraint next = iter.getNext();
						Unit unit = mapping.get(next).clone();
						unit.setNeg();
						T.unitPropagate(unit, chrono);
						bias_minus.getNetwork().remove(next);
						iter.next();
						kappaexp_size++;

					}
					}
					else {
						KappaIterator2 iter = new KappaIterator2(constrSolver, archtype, vars, bias, exp,
								membership_query, network, constraintFactory, chrono, solvoptim, knownconstraints.network);
						//int i=0;
						while (iter.hasNext()) {
							ACQ_IConstraint next = iter.getNext();
							if(bias_minus.contains(next)) {
								Unit unit = mapping.get(next).clone();
								unit.setNeg();
								T.unitPropagate(unit, chrono);
								bias_minus.getNetwork().remove(next);
							}
							
							iter.next();
							kappaexp_size++;

						}

					}
					chrono.stop("explanation_solver_time_pos_query");
					if(!bias_optim) {
						
					learned.getLearnedNetwork(T);
					learner.infexppos(answer.getValue(),kappa2.size(), kappaexp_size);
					}
					learner.solvtimehistory(1, chrono.getLast("explanation_solver_time_pos_query", TimeUnit.S));
					chrono.reset("explanation_solver_time_pos_query");
					
					if(bias_optim) {
						assert kappaexp_size >= kappa.size() : "kappa is more informative than exp";

					}
					else {
						assert kappaexp_size >= kappa2.size() : "kappa is more informative than exp";

					}

				} else {

					if (kappa.size() == 1) {
						chrono.stop("first_constr_learned");
						ACQ_IConstraint c = kappa.get_Constraint(0);
						Unit unit = mapping.get(c).clone();
						T.unitPropagate(unit, chrono);
						Clause unary = new Clause(unit);
						unary.setOriginQuery(membership_query);
						T.add(unary);

						// Remove negation
						bias_minus.reduce(c.getNegation());
						unit = mapping.get(c.getNegation()).clone();
						unit.setNeg();
						T.unitPropagate(unit, chrono);
						

					} else {

						Clause disj = new Clause();
						for (ACQ_IConstraint c : kappa) {
							
							Unit unit = mapping.get(c).clone();
							disj.add(unit);
							
						}
						disj.setOriginQuery(membership_query);
						T.add(disj);
					}
					if(answer==Answer.UKN) {
						learned.getLearnedNetwork(T);
						learner.infexpneg(answer.getValue(),kappa.size(), 0);

					}
					if (answer == Answer.NO) {
						if(bias_optim) {
							int b = 0;
							ACQ_Network network = new ACQ_Network(constraintFactory, bias.getVars());
							network.getLearnedNetwork(T);
							chrono.start("explanation_solver_time_neg_query");
							b = b + generelize_simple_learned(exp.getNegation(), membership_query);
							chrono.stop("explanation_solver_time_neg_query");
							learned.getLearnedNetwork(T);

							learner.infexpneg(answer.getValue(),kappa.size(), b);
							learner.solvtimehistory(0, chrono.getLast("explanation_solver_time_neg_query", TimeUnit.S));
							chrono.reset("explanation_solver_time_neg_query");
						}
						else {
							int b = 0;
							// listnegexp.add(exp.getNegation());
							ACQ_Network network = new ACQ_Network(constraintFactory, bias.getVars());
							learned.getLearnedNetwork(T);
							chrono.start("explanation_solver_time_neg_query");{
								
							}
							b=b+generelize_simple_learned2(exp.getNegation(), membership_query);

							chrono.stop("explanation_solver_time_neg_query");
							learned.getLearnedNetwork(T);

							learner.infexpneg(answer.getValue(),kappa2.size(),b);
							learner.solvtimehistory(0, chrono.getLast("explanation_solver_time_neg_query", TimeUnit.S));
							

						}

					}

				}
			}
			nbquery++;
		}

		chrono.stop("total_acq_time");
		chrono.stop("ct_found");
		
		CNF F = T.clone();
		for (ACQ_IConstraint c : bias.getConstraints()) {
			if (bias_minus.contains(c))
				continue;
			Unit u = mapping.get(c).clone();
			u.setNeg();
			F.add(new Clause(u));
		}
		
		for(Clause u: T) {
			if(!bias_minus.contains(u.get(0).getConstraint()) && (! u.get(0).isNeg())){
				ACQ_IConstraint c = u.get(0).getConstraint();
				collapse = true;
				break;
			}
		}
		
		if (this.timeouted) {
			if (verbose)
				System.out.println("[WARNING] Timeouted");
			learned_network = bias_minus.getNetwork();
		} else if (!collapse) {
			if (verbose)
				System.out.print("[INFO] Extract network from T: ");
			SATModel model = satSolver.solve(F);
			if (verbose)
				System.out.println("Done");
			learned_network = model != null ? toNetwork(model) : null;
			assert learned_network!= null;
		}

		return !collapse;

	}


	protected ACQ_Network toNetwork(SATModel model) throws Exception {
		chrono.start("to_network");
		assert (model != null);
		ACQ_Network network = new ACQ_Network(constraintFactory, bias.getVars());

		for (ACQ_IConstraint constr : model.getPositive()) {
			assert constr != null;
			network.add(constr, true);
		}

		chrono.stop("to_network");
		return network;
	}


}
