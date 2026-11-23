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
/*  for more details (enclosed in the file licensesLGPLv2.1).              */
/*                                                                          */
/****************************************************************************/

package io.github.binsec.core;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.TimeoutException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import io.github.binsec.core.acqconstraint.ACQ_DisjunctionConstraint;
import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqconstraint.ConstraintFactory;
import io.github.binsec.core.acqconstraint.ConstraintMapping;
import io.github.binsec.core.acqconstraint.Contradiction;
import io.github.binsec.core.acqconstraint.ContradictionSet;
import io.github.binsec.core.acqconstraint.Unit;
import io.github.binsec.core.acqconstraint.ConstraintFactory.ConstraintSet;
import io.github.binsec.core.acqsolver.ACQ_BitwuzlaSolver;
import io.github.binsec.core.acqsolver.ACQ_ConstraintSolver;
import io.github.binsec.core.acqsolver.SATSolver;
import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.acqvariable.ACQ_Variable;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.combinatorial.CombinationIterator;
import io.github.binsec.core.combinatorial.MARCO;
import io.github.binsec.core.combinatorial.MARCO2;
import io.github.binsec.core.combinatorial.MSSEnumIter;
import io.github.binsec.core.combinatorial.MSSIter;
import io.github.binsec.core.combinatorial.SubMSSIterator;
import io.github.binsec.core.combinatorial.SubMSSIterator.Strategy;
import io.github.binsec.core.learner.ACQ_Bias;
import io.github.binsec.core.learner.ACQ_Learner;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.learner.Answer;
import io.github.binsec.core.learner.Explanation;
import io.github.binsec.core.learner.ObservedLearner;
import io.github.binsec.core.tools.ArchType;
import io.github.binsec.core.tools.Chrono;
import io.github.binsec.core.tools.QueryPrinter;
import io.github.binsec.core.tools.TimeUnit;

public class ACQ_XDCA {

	protected ArrayList<ACQ_Query> queries = new ArrayList<>();
	protected ACQ_Bias atomic = null; 
	protected ACQ_Bias knownconstraints = null; 
	protected SATSolver satSolver;
	protected ACQ_BitwuzlaSolver solver;
	protected ACQ_Learner learner;
	protected ACQ_Network learned_dnf = null;
	protected ConstraintMapping mapping = null;
	protected int disj = 0;
	Chrono chrono;
	
	protected ArrayList<ACQ_Network> muses = null;
	protected Long learningtimeout;
	protected Long t0;
	protected ArrayList<ACQ_Network> strategy = null;
	protected ContradictionSet backgroundKnowledge = null;
	protected boolean verbose = false;
	protected boolean grow2 = true;
	public boolean timeouted = false;
	public ArchType archtype;
	protected QueryPrinter qp = null;
	protected SubMSSIterator.Strategy submssStrategy = SubMSSIterator.Strategy.QUICKEXPLAIN;
	private boolean neg_activated;
	private boolean pos_activated;

	private ACQ_CellVariable[] cells;
	private ArrayList<String> learnedNegMSSes=new ArrayList<>();;
	private ArrayList<String> learnedPosMSSes=new ArrayList<>();;
	private ArrayList<String> learnedNegMCS=new ArrayList<>();;
	private ArrayList<String> learnedPosMCS=new ArrayList<>();;
	
	public ACQ_XDCA(ACQ_Bias bias, ACQ_Bias known, ACQ_Learner learn, SATSolver sat, ACQ_BitwuzlaSolver solver2
			, ArchType archtype, boolean neg_activated, boolean pos_activated, 
			ACQ_CellVariable[] cells) {
		learner = learn;
		satSolver = sat;
		solver = solver2;
		atomic = bias;
		knownconstraints = known;
		this.archtype= archtype;
		this.neg_activated=neg_activated;
		this.pos_activated=pos_activated;

		this.cells=cells;
		mapping = new ConstraintMapping();
		

		
		for (ACQ_IConstraint c : bias.getConstraints()) {
			String newvarname = c.getName() + c.getVariables();
			Unit unit = this.satSolver.addVar(c, newvarname);
			this.mapping.add(c, unit);
			
			ACQ_IConstraint neg = c.getNegation();
			assert bias.contains(neg) : "Bias should be complete";
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
		
		assert mapping.size() >= bias.getSize(): "mapping must contain more elements than bias";
		
	}
	

	public void setSubmssStrategy(SubMSSIterator.Strategy strategy) {
	    this.submssStrategy = strategy;
	}
	
	public void setVerbose(boolean verbose) {
		this.verbose = verbose;
	}
	
	public void setQueryPrinter(QueryPrinter qp) {
		this.qp = qp;
	}
	
	public void setGrow2(boolean b) {
		grow2 = b;
	}
	
	public void setLearningTimeout(Long tm) {
		this.learningtimeout = tm;
	}
	
	public void setStrat(ArrayList<ACQ_Network> strat) {
		this.strategy = strat;
	}
	
	public void setBackgroundKnowledge(ContradictionSet back) {
		this.backgroundKnowledge = back;
	}
	
	public ACQ_Network getLearnedDNF() {
		return this.learned_dnf;
	}
	
	public Boolean process(Chrono chronom) throws Exception {
		t0 = System.currentTimeMillis();
		chrono = chronom;
		chrono.start("last_no");
		
		ConstraintFactory fact = this.atomic.getNetwork().getFactory();
		ACQ_Network res = new ACQ_Network(fact, this.atomic.getNetwork().getVariables());
		ACQ_Network empty = new ACQ_Network(fact, this.atomic.getNetwork().getVariables());
		
		
		MSSIter iter = new MARCO2(atomic, empty, solver, satSolver, mapping, 
				backgroundKnowledge, knownconstraints, learningtimeout, grow2, chrono);
		
		while (iter.hasNext()) {
			Explanation exp = new Explanation();
			if (System.currentTimeMillis() - t0 > learningtimeout) {
				timeouted = true;
				this.learned_dnf = res;
				this.muses = iter.getMuses();
				return false;
			}
			ACQ_Query query;
			try {
				query = iter.next();
			}
			catch (TimeoutException e) {
				timeouted = true;
				this.learned_dnf = res;
				this.muses = iter.getMuses();
				return false;
			}
			if (verbose) System.out.print(qp.toString(query));
			ACQ_Network ss=null;
			ACQ_Network mss;

			Answer answer = learner.ask(query, exp);
			if(answer!=Answer.YES) {
				chrono.markReplace("last_no");
			}
			mss=iter.queryToMss(query);
			
			if (verbose) System.out.println("::" + query.getClassification());
				if (answer != Answer.UKN) {
						if((answer==Answer.NO)&&(neg_activated)) {
							try {
								ss = exp_shrink(mss, exp, query);
							}
							catch (TimeoutException e) {
								timeouted = true;
								this.learned_dnf = res;
								this.muses = iter.getMuses();
								return false;
							}
						}
						
					else if ((answer==Answer.YES)&&(pos_activated)) ss = exp_shrink(mss, exp, query);
					if(ss==null) {
						if(answer ==Answer.NO) {
							ACQ_IConstraint toadd = removeMSS(query, atomic);
							res.add(toadd, true);
						}
					
					iter.BlockDownFormula2(mss);
					ss=mss;
					}
					else {
						if(answer ==Answer.NO) {
							ACQ_IConstraint toadd = removeSubMSS(ss);
							res.add(toadd, true);
							//iter.BlockDownFormula2(ss);
						}
						//System.out.println("MINIMISATION RESULT: "+ss.toString());
						learner.updateExpStat(answer.getValue(),mss.size(),ss.size());
						iter.BlockDownFormula2(ss);
						iter.unitPropagation(ss);

					}
					if(answer==Answer.NO) {
						learnedNegMSSes.add(mss.toSmtlib());
						learnedNegMCS.add(ss.toSmtlib());

					}
					else {
						learnedPosMSSes.add(mss.toSmtlib());
						learnedPosMCS.add(ss.toSmtlib());
					}
				}
				else {
					ACQ_IConstraint toadd = removeMSS(query, atomic);
					res.add(toadd, true);
					iter.BlockDownFormula2(mss);
				}
				
			chrono.start("gen_query");
			iter.advance();
			chrono.stop("gen_query");

		}
		this.timeouted = false;
		this.learned_dnf = res;
		this.muses = iter.getMuses();
		return false;
		
	}
	
	
	
	private ACQ_Network exp_shrink(ACQ_Network ss, Explanation exp, ACQ_Query query) throws TimeoutException {
	    ACQ_Network res = null;
	    if(submssStrategy!=Strategy.QUICKEXPLAIN) {
	    SubMSSIterator submss = new SubMSSIterator(ss, disj, submssStrategy);

		    while (submss.hasNext()) {
		    	if (System.currentTimeMillis() - t0 > learningtimeout) {
	                timeouted = true;
	                return null;
	            }
		        ACQ_Network candidate = submss.next();
		        if(query.isNegative()) {
		        	chrono.start("explanation_solver_time_neg");
					chrono.start("explanation_solver_time_neg_query");

		        }
		        else {
		        	chrono.start("explanation_solver_time_pos");
					chrono.start("explanation_solver_time_pos_query");

		        }
		        boolean worked = !solver.solveSubmss(candidate, knownconstraints.network, exp.getNegation(), archtype, query);
		        
		        if(query.isNegative()) {
		        	chrono.stop("explanation_solver_time_neg");
		        	learner.solvtimehistory(0, chrono.getLast("explanation_solver_time_neg_query", TimeUnit.S));
					chrono.reset("explanation_solver_time_neg_query");
		        }
		        else {
		        	chrono.stop("explanation_solver_time_pos");
		        	learner.solvtimehistory(1, chrono.getLast("explanation_solver_time_pos_query", TimeUnit.S));
					chrono.reset("explanation_solver_time_pos_query");
		        }
		        
		        if (worked) {
		            res = candidate;
		            break;
		        }
		    }
	    }
	    else {
	    	if(query.isNegative()) {
	        	chrono.start("explanation_solver_time_neg");
				chrono.start("explanation_solver_time_neg_query");

	        }
	    	else {
	        	chrono.start("explanation_solver_time_pos");
				chrono.start("explanation_solver_time_pos_query");

	        }
	    	try {
	    		
	    	
	    	res=quickExplain(exp,ss,exp.getRegId(),query);
	    	if(query.isNegative()) {
	        	chrono.stop("explanation_solver_time_neg");
				chrono.stop("explanation_solver_time_neg_query");
	        	learner.solvtimehistory(0, chrono.getLast("explanation_solver_time_neg_query", TimeUnit.S));
				chrono.reset("explanation_solver_time_neg_query");
	        }
	        else {
	        	chrono.stop("explanation_solver_time_pos");
				chrono.stop("explanation_solver_time_pos_query");

	        	learner.solvtimehistory(1, chrono.getLast("explanation_solver_time_pos_query", TimeUnit.S));
				chrono.reset("explanation_solver_time_pos_query");
	        }
	    	}
	    	catch (TimeoutException e) {
	    		throw new TimeoutException();
			}
	    }
	    
	    return res;
	}

	protected ACQ_DisjunctionConstraint removeMSS(ACQ_Query e, ACQ_Bias bias) {
		ConstraintFactory fact = bias.getNetwork().getFactory();
		ConstraintSet set = fact.createSet();
		for (ACQ_IConstraint c : bias.getConstraints()) {
			if (c.check(e)) {
				set.add(c.getNegation());
				//System.out.println(c);
			}
		}
		return new ACQ_DisjunctionConstraint(fact, set);
	}
	
	protected ACQ_DisjunctionConstraint removeSubMSS(ACQ_Network submss) {
		//System.out.println("\nTO ADD"+submss.toString());
		ConstraintFactory fact = submss.getFactory();
		ConstraintSet set = fact.createSet();
		for (ACQ_IConstraint c : submss) {
				set.add(c.getNegation());
		}
		return new ACQ_DisjunctionConstraint(fact, set);
	}
	
	protected boolean istimeouted() throws TimeoutException {
		if (learningtimeout != null && 
				(learningtimeout <= (System.currentTimeMillis() - t0))) {
			throw new TimeoutException();
		}
		
		return false;
	}
	
	protected ACQ_Network quickExplain(Explanation exp, ACQ_Network network, Map<String, String> regid, ACQ_Query q) throws TimeoutException  {
		
		istimeouted();
		chrono.start("quick_explain");
		ACQ_Network res=null;
		//System.out.println(exp.getExp());
		
			//System.out.println(exp.getExp());
			res = quick(exp.getNegation().getExp(), exp.getNegation().getExp(), network, regid,q);
			//System.out.print(res);
			if(res.size()==network.size()) return network;
			assert !isConsistent(exp.getNegation().getExp()+res.toBw(q,regid)+"\n",regid, q) : "quickExplain must returned inconsistent networks";
			//result = new Contradiction(res);
		
		chrono.stop("quick_explain");
		res.toValid(network);
		return res;
	}
	
	protected ACQ_Network quick(String expP1, String p2, ACQ_Network c, Map<String, String> regid, ACQ_Query q ) {
		if (countAssert(p2) != 0 && !isConsistent(expP1,regid, q)) {
			return new ACQ_Network(c.getFactory(), c.getFactory().createSet());
		}
		if (c.size() == 1)
			return c;

		ACQ_Network c1 = new ACQ_Network(atomic.network.getFactory(), atomic.network.getVariables());
		ACQ_Network c2 = new ACQ_Network(atomic.network.getFactory(), atomic.network.getVariables());

		int i = 0;
		for (ACQ_IConstraint constr : c.getConstraints()) {
			if (i < c.size() / 2) {
				c1.add(constr, true);
			} else {
				c2.add(constr, true);
			}
			i += 1;
		}

		String b_union_c1 = expP1+"\n"+c1.toBw(q,regid);
		//System.out.println(expP1);
		ACQ_Network delta2 = quick(b_union_c1, c1.toBw(q,regid), c2, regid, q);

		String b_union_delta2 = expP1+"\n"+delta2.toBw(q,regid);
		ACQ_Network delta1 = quick(b_union_delta2, delta2.toBw(q,regid), c1, regid, q);

		delta1.addAll(delta2, true);
		return delta1;
	}

	
	
	

	private int countAssert(String p2) {
		if (p2 == null || p2.isEmpty()) {
	        return 0;
	    }

	    int count = 0;
	    Pattern pattern = Pattern.compile("\\(\\s*assert\\b");
	    
	    String[] lines = p2.split("\\r?\\n");
	    
	    for (String line : lines) {
	        int commentIndex = line.indexOf(';');
	        if (commentIndex != -1) {
	            line = line.substring(0, commentIndex);
	        }
	        
	        Matcher matcher = pattern.matcher(line);
	        while (matcher.find()) {
	            count++;
	        }
	    }
	    
	    return count;
	}

	protected Boolean isConsistent(String exp, Map<String, String> regid, ACQ_Query q) {
		//System.out.println(exp);
		boolean res = solver.solve(exp, regid, archtype, q).booleanValue();
		return res;
	}
	
	public ArrayList<String> getLearnedNegMSSes() {
	    return this.learnedNegMSSes;
	}
	
	public ArrayList<String> getLearnedPosMSSes() {
	    return this.learnedPosMSSes;
	}
	
	public ArrayList<String> getLearnedNegMCS() {
	    return this.learnedNegMCS;
	}
	
	public ArrayList<String> getLearnedPosMCS() {
	    return this.learnedPosMCS;
	}
	
}


