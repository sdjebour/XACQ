package io.github.binsec.core.acqsolver;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.math.BigInteger;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.acqvariable.ACQ_Variable;
import io.github.binsec.core.acqvariable.CellType;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.learner.Explanation;
import io.github.binsec.core.tools.ArchType;
import io.github.binsec.core.tools.Chrono;

public class ACQ_BitwuzlaSolver extends ACQ_ConstraintSolver {

	ACQ_CellVariable[] cells;
	String base_smtlib = "";
	ArrayList<String> acq_vars = new ArrayList<>();
	Runtime runtime;
	String block_list="";

	private String base_smtlib2;

	public ArrayList<String> get_acq_vars() {
		return this.acq_vars;
	}

	public String getBaseFile(ArchType archtype, Explanation exp, ACQ_Query q) {

		return base_smtlib + "\n" + exp.getExp() + "\n" + ptr_bk(cells, archtype, exp.getRegId(), q) + "\n";

	}

	public ACQ_BitwuzlaSolver(ACQ_CellVariable[] cells, int maxcoeff, Chrono chrono, ArchType archtype) {
		this.cells = cells;
		this.runtime = Runtime.getRuntime();
		base_smtlib = "(set-logic QF_ABV)\n" + "(set-option :produce-models true)\n"
				+ "(set-option :print-success false)\n\n";

		base_smtlib2 = "(set-logic QF_ABV)\n" + "(set-option :produce-models true)\n"
				+ "(set-option :print-success false)\n\n";

		for (ACQ_CellVariable cell : cells) {
			if (cell.isGlobal()) {
				int type_sz = CellType.PTR.getSize(archtype);
				// declare pointer
				base_smtlib += String.format("(declare-fun v%d () (_ BitVec %d))\n", cell.getRef().id, type_sz);
				// assert domain of the pointer
				base_smtlib += String.format("(assert %s)\n", cell.getRefBwDomain());
				acq_vars.add(String.format("v%d", cell.getRef().id));
			}

			int type_sz = cell.getType().getSize(archtype);
			// TODO put arch_size
			switch (cell.getType()) {
			case STR:
				base_smtlib += String.format("(declare-fun v%d () (_ BitVec %d))\n", cell.getValue().id, type_sz);
				base_smtlib += String.format("(assert %s)\n", cell.getValueBwDomain());
				// for the size of the string
				base_smtlib += String.format("(declare-fun v%d () (_ BitVec 16))\n", cell.getSize().id);
				base_smtlib += String.format("(assert %s)\n", cell.getSizeBwDomain());
				acq_vars.add(String.format("v%d", cell.getValue().id));
				acq_vars.add(String.format("v%d", cell.getSize().id));
				break;

			case PTR:
			case INT:
			case INT8:
			case UINT:
			case UINT8:
			case UINT16:
			case BOOL:
				base_smtlib += String.format("(declare-fun v%d () (_ BitVec %d))\n", cell.getValue().id, type_sz);
				base_smtlib += String.format("(assert %s)\n", cell.getValueBwDomain());
				acq_vars.add(String.format("v%d", cell.getValue().id));
				break;
			default:
				assert false;

			}
		}
		//System.out.println("LA BASE : "+base_smtlib);
	}

	/*
	 * public ACQ_BitwuzlaSolver(CellWithSizeVariable[] cells, int maxcoeff) {
	 * this.cells = cells; this.runtime = Runtime.getRuntime();
	 * 
	 * base_smtlib = "(set-logic QF_ABV)\n" + "(set-option :produce-models true)\n"
	 * + "(set-option :print-success false)\n\n";
	 * 
	 * 
	 * for (CellWithSizeVariable cell: cells) { if (cell.isGlobal()) { base_smtlib
	 * += String.format("(declare-fun v%d () (_ BitVec 32))\n", cell.getRef().id);
	 * base_smtlib += String.format("(assert %s)", cell.getRefBwDomain(8));
	 * acq_vars.add(String.format("v%d", cell.getRef().id)); } base_smtlib +=
	 * String.format("(declare-fun v%d () (_ BitVec 32))\n", cell.getValue().id);
	 * base_smtlib += String.format("(assert %s)", cell.getValueBwDomain(8));
	 * acq_vars.add(String.format("v%d", cell.getValue().id));
	 * 
	 * switch (cell.getType()) { case PTR: base_smtlib +=
	 * String.format("(declare-fun v%d () (_ BitVec 32))\n", cell.getSize().id);
	 * base_smtlib += String.format("(assert %s)", cell.getSizeBwDomain(8));
	 * acq_vars.add(String.format("v%d", cell.getSize().id)); break;
	 * 
	 * case INT: case UINT: case UINT8: case UINT16: case BOOL: break; default:
	 * assert false;
	 * 
	 * }
	 * 
	 * }
	 * 
	 * }
	 */

	private String toSmtlib(ACQ_Network net) {
		String res = "";
		// = base_smtlib;

		for (ACQ_IConstraint constr : net.getConstraints()) {
			// System.out.println(constr.getName());
			res += "\n(assert " + constr.getBwConstraint() + ")";
		}

		// res += "\n(check-sat)\n" + "(get-model)\n" + "(exit)";

		// System.out.println(res);
		return res;
	}

	private String toSmtlib2(ACQ_Network net, ACQ_Query q, Map<String, String> regid) {
		String res = "";

		for (ACQ_IConstraint constr : net.getConstraints()) {
			// System.out.println(constr.getName());
			res += "\n(assert " + constr.toBinsecConstraint(q, regid) + ")";
		}

		// res += "\n(check-sat)\n" + "(get-model)\n" + "(exit)";

		// System.out.println(res);
		return res;
	}
	
	private String toSmtlib3(ACQ_Network net, ACQ_Query q, Map<String, String> regid) {
		String res = "";

		for (ACQ_IConstraint constr : net.getConstraints()) {
			// System.out.println(constr.getName());
			res += "\n(assert " + constr.toBinsecConstraint(q, regid) + ")";
		}
		for(ACQ_CellVariable cell : cells) {
			if(cell.getType()==CellType.PTR) {
				String toadd="";
				if (!regid.get("x" + cell.cellid).isEmpty())
					toadd = "!" + regid.get("x" + cell.cellid);
				String val1_value = "x" + cell.cellid + toadd;

				int n = cell.getType().getSize(cell.arch) / 4;
				String hexcst = "#x" + String.format("%0" + n + "x", 0);
				res+= String.format("(assert (bvsge %s %s))", val1_value, hexcst);
			}
		}

		// res += "\n(check-sat)\n" + "(get-model)\n" + "(exit)";

		// System.out.println(res);
		return res;
	}

	private BitwuzlaAnswer call(ACQ_Network net) {
		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(toSmtlib(net));
			myWriter.write("\n(check-sat)\n" + "(get-model)\n" + "(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;
		Bitvec[] model = new Bitvec[acq_vars.size()];

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				} else if (s.contains("define-fun")) {
					Pattern p = Pattern.compile("\\(define-fun v(\\d+) \\(\\) \\(_ BitVec (\\d+)\\) #b([01]+)\\)");
					Matcher m = p.matcher(s.strip());
					if (m.matches()) {
						int varid = Integer.parseInt(m.group(1));
						Bitvec value = new Bitvec(new BigInteger(m.group(3), 2), Integer.parseInt(m.group(2)));
						model[varid] = value;
					}
				}
			}
			s = "";
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		if (sat) {
			return new BitwuzlaAnswer(sat, new ACQ_Query(net.getVariables(), model));
		} else {
			return new BitwuzlaAnswer(sat, new ACQ_Query());
		}
	}

	@Override
	public boolean solve(ACQ_Network learned_network) {
		fireSolverEvent("BEG_solve_network", false, true);

		BitwuzlaAnswer answer = call(learned_network);

		fireSolverEvent("END_solve_network", true, false);
		return answer.sat;
	}

	public BitwuzlaAnswer solve_check_constraint(ACQ_Query q, ACQ_Network bk, Explanation exp, ACQ_CellVariable[] cells,
			ArchType archtype, ACQ_IConstraint c, Chrono chrono) {
		fireSolverEvent("BEG_solve_network", false, true);

		BitwuzlaAnswer answer = call_check_constraint(q, bk, exp, cells, archtype, c, chrono);

		fireSolverEvent("END_solve_network", true, false);
		return answer;
	}

	/*
	 * public BitwuzlaAnswer solve_get_model(Explanation exp, ACQ_Scope scope,
	 * ACQ_CellVariable[] cells, ArchType archtype, ACQ_Query q) {
	 * fireSolverEvent("BEG_solve_network", false, true);
	 * 
	 * BitwuzlaAnswer answer = call_get_model(exp, scope, cells, archtype, q);
	 * 
	 * fireSolverEvent("END_solve_network", true, false); return answer; }
	 */
	
	  public void block_model(Bitvec[] model) { 
		  String toadd="(assert (not (and ";
		  for(int i=0;i<model.length;i++) {
			 toadd=toadd+"(= v"+i+" "+model[i].toHex()+")";
		  }
		  toadd = toadd+")))\n";
		  block_list=block_list+"\n"+toadd;
	  }
	 

	private BitwuzlaAnswer call_check_constraint(ACQ_Query q, ACQ_Network bk, Explanation exp, ACQ_CellVariable[] cells,
			ArchType archtype, ACQ_IConstraint c, Chrono chrono) {

		String ptr_bk = ptr_bk(cells, archtype, exp.getRegId(), q);
		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			myWriter.write(base_smtlib2);
			myWriter.write(exp.getExp());
			myWriter.write(ptr_bk);
			myWriter.write("(assert " + c.toBinsecConstraint(q, exp.getRegId()) + ")\n");
			myWriter.write(toSmtlib2(bk, q, exp.getRegId()));
			myWriter.write("(check-sat)\n(exit)");
			myWriter.close();
			// System.out.println(base_smtlib+exp.getExp()+asserts+"(assert "
			// +c.getBwConstraint()+")\n"+asserts2+"(check-sat)\n(exit)");

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;
		// System.out.println("start call : "+temp.getName());

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };
			chrono.start("explanation_solver_time_pos");
			proc = runtime.exec(torun);
			proc.waitFor();
			chrono.stop("explanation_solver_time_pos");

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;
		Bitvec[] model = new Bitvec[acq_vars.size()];

		String s;
		String s2 = "";
		String s3 = "";
		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;
				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}

			}
			// System.out.println(s2);
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert sat != null : s3;
		return new BitwuzlaAnswer(sat, new ACQ_Query());

	}

	// add all the necessary asserts between the registers and the acquisition
	// variables
	private String ptr_bk(ACQ_CellVariable[] cells, ArchType archtype, Map<String, String> regid, ACQ_Query q) {
		String res = "";

		// add a 1 size bv that represent the msb
		int n = archtype.getPtrSize() - 1;
		// int n_minus = n - 1;

		for (ACQ_CellVariable cell : cells) {
			if (cell.getType().isPtrKind()) {
				String toadd = "";
				if (!regid.get("x" + cell.cellid).isEmpty())
					toadd = "!" + regid.get("x" + cell.cellid);

				res += String.format("(assert (= ((_ extract %d %d ) x%d%s) #b0))\n", n, n, cell.cellid, toadd);
			}

		}
		//System.out.println(res);
		return res;
	}

	/*
	 * private BitwuzlaAnswer call_get_model(Explanation exp, ACQ_Scope scope,
	 * ACQ_CellVariable[] cells, ArchType archtype, ACQ_Query q) { BufferedReader
	 * stdInput = null; FileWriter myWriter; File temp = null; try { temp =
	 * File.createTempFile("bitwuzla_", ".txt"); myWriter = new FileWriter(temp);
	 * myWriter.write(base_smtlib); myWriter.write(exp.getExp());
	 * myWriter.write(asserts(cells, archtype, exp.getRegId(), q));
	 * myWriter.write("(check-sat)\n(get-model)\n(exit)"); myWriter.close(); } catch
	 * (IOException e) { // TODO Auto-generated catch block e.printStackTrace(); }
	 * assert temp != null : "temp file should not be null";
	 * 
	 * Process proc;
	 * 
	 * try { String[] torun = new String[] { String.format("%s/resources/bitwuzla",
	 * System.getenv("PRECA_PATH")), "-m", // "-t" , String.format("%l",
	 * getLimit()), temp.getPath(), };
	 * 
	 * proc = runtime.exec(torun); proc.waitFor();
	 * 
	 * stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
	 * 
	 * Files.deleteIfExists(temp.toPath()); } catch (IOException |
	 * InterruptedException e1) { // TODO Auto-generated catch block
	 * e1.printStackTrace(); }
	 * 
	 * Boolean sat = null; Bitvec[] model = new Bitvec[acq_vars.size()];
	 * 
	 * String s; try { while ((s = stdInput.readLine()) != null) { //
	 * System.out.println(s); if (s.contains("unsat")) { sat = false; } else if
	 * (s.contains("unknown")) { assert false; } else if (s.contains("sat")) { sat =
	 * true; } else if (s.contains("define-fun")) { Pattern p =
	 * Pattern.compile("\\(define-fun v(\\d+) \\(\\) \\(_ BitVec 32\\) #b(\\d+)\\)"
	 * ); Matcher m = p.matcher(s.strip()); if (m.matches()) { int varid =
	 * Integer.parseInt(m.group(1)); Bitvec value = new Bitvec(new
	 * BigInteger(m.group(2), 2), 32); model[varid] = value; System.out.println("V"
	 * + varid + " = " + value); }
	 * 
	 * } } } catch (IOException e) { // TODO Auto-generated catch block
	 * e.printStackTrace(); }
	 * 
	 * if (sat) { exp.setExp(exp.getExp() + block_model(model)); return new
	 * BitwuzlaAnswer(sat, new ACQ_Query(scope, model)); } else { return new
	 * BitwuzlaAnswer(sat, new ACQ_Query()); } }
	 */

	@Override
	public ACQ_Query solveQ(ACQ_Network learned_network) {
		fireSolverEvent("BEG_solveQ", false, true);
		BitwuzlaAnswer answer = call(learned_network);
		fireSolverEvent("END_solveQ", true, false);
		return answer.query;

	}

	@Override
	public ACQ_Query peeling_process(ACQ_Network network_A, ACQ_Network network_B) {
		assert false;
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setVars(ACQ_Scope vars) {
		// TODO Auto-generated method stub

	}

	@Override
	public ACQ_Query max_AnotB(ACQ_Network network1, ACQ_Network network2, ACQ_Heuristic heuristic) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected ArrayList<ACQ_Query> allSolutions(ACQ_Network learned_network) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected void setTimeoutReached(boolean timeoutReached) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isTimeoutReached() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public ACQ_Network get2remove() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void reset2remove() {
		// TODO Auto-generated method stub

	}

	@Override
	public ACQ_IDomain getDomain() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean equiv(ACQ_Network net1, ACQ_Network net2, ACQ_Network known) {
		// Check that net1 and net2 are equivalent modulo known context

		// check ~net1 /\ net2
		ACQ_Network new1 = new ACQ_Network(net2.constraintFactory, net2, net2.getVariables());
		new1.add(net1.getNegation(), true);
		new1.addAll(known, true);
		if (!solveQ(new1).isEmpty())
			return false;

		// check net1 /\ ~net2
		ACQ_Network new2 = new ACQ_Network(net1.constraintFactory, net1, net1.getVariables());
		new2.add(net2.getNegation(), true);
		new2.addAll(known, true);
		if (!solveQ(new2).isEmpty())
			return false;

		return true;
	}

	public boolean solveGen(ACQ_IConstraint c, Explanation exp, ACQ_Network bk, ArchType archtype, ACQ_Query q) {
		// System.out.println(c.getName());
		BufferedReader stdInput = null;
		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(toSmtlib(bk));
			myWriter.write(exp.getExp());
			myWriter.write(ptr_bk(cells, archtype, exp.getRegId(), q));
			myWriter.write("\n (assert" + c.toBinsecConstraint(q, exp.getRegId()) + ")\n");
			myWriter.write("(check-sat)\n(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;

		String s;
		String s2 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);

		return sat;

	}

	public boolean solveGen(ACQ_IConstraint c, ACQ_Network learned, ACQ_Network bk, Explanation exp, ArchType archtype,
			Chrono chrono, ACQ_Query q) {

		BufferedReader stdInput = null;
		BufferedReader stdErr = null;
		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib2);
			myWriter.write(exp.getExp());
			myWriter.write(ptr_bk(cells, archtype, exp.getRegId(), q));
			myWriter.write("\n (assert" + c.toBinsecConstraint(q, exp.getRegId()) + ")\n");
			myWriter.write(toSmtlib2(learned, q, exp.getRegId()));
			myWriter.write("\n(check-sat)\n" + "(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;
		chrono.start("explanation_solver_time_neg");

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			chrono.stop("explanation_solver_time_neg");

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		return sat;
	}
	
	public boolean solveSubmss(ACQ_Network submss, ACQ_Network bk, Explanation exp, ArchType archtype,
		 ACQ_Query q) {

		BufferedReader stdInput = null;
		BufferedReader stdErr = null;
		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib2);
			myWriter.write(exp.getExp());
			myWriter.write(ptr_bk(cells, archtype, exp.getRegId(), q));
			
			for(ACQ_IConstraint c : submss) { 
				myWriter.write("\n (assert" + c.toBinsecConstraint(q, exp.getRegId()) + ")\n");
			}
			myWriter.write("\n(check-sat)\n" + "(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));


			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		return sat;
	}

	public String size_assert(ACQ_Query q, ArchType arch) {
		String res = "";
		int nbrptr = 0;
		int n = CellType.PTR.getSize(arch);
		for (ACQ_CellVariable cell : cells) {
			if (cell.getType() == CellType.STR) {
				if (cell.isGlobal()) {
					for (ACQ_CellVariable cell2 : cells) {
						if (!cell2.isGlobal()) {
							if (q.getValue(cell.getRef().id).unsigned().intValue() == q.getValue(cell2.getValue().id)
									.unsigned().intValue()) {
								res += String.format(" (= v%d v%d)", cell2.getValue().id, cell.getRef().id);
							} else {
								res += String.format(" (not (= v%d v%d))", cell2.getValue().id, cell.getRef().id);
							}
						}
					}
				}
				nbrptr++;
				String strlen = String.format("#x%04x", q.getValue(cell.getSize().id).unsigned().intValue());
				String val_size = "v" + cell.getSize().id;
				res += String.format(" (= %s %s) ", val_size, strlen);
			}
		}
		if (nbrptr == 0)
			return "";
		if (nbrptr == 1)
			return "(assert " + res + ")";

		return "(assert (and" + res + "))";
	}

	public boolean solve(ACQ_IConstraint c, ACQ_Query q, ACQ_Network network, ACQ_Network learned, ArchType arch,
			Chrono chrono) {

		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(toSmtlib(network));
			myWriter.write(toSmtlib(learned));
			myWriter.write("\n(assert" + c.getBwConstraint() + ")\n");
			myWriter.write(size_assert(q, arch) + "\n");

			myWriter.write("(check-sat)\n(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;
		chrono.start("explanation_solver_time_neg");

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		chrono.stop("explanation_solver_time_neg");

		Boolean sat = null;

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		return sat;
	}

	public boolean solve_pos(ACQ_IConstraint c, ACQ_Network bk, ACQ_Query q, ArchType arch) {

		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(toSmtlib(bk));
			myWriter.write("\n(assert" + c.getBwConstraint() + ")\n");
			myWriter.write(size_assert(q, arch) + "\n");

			myWriter.write("(check-sat)\n(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		return sat;
	}

	public boolean check_consistancy(ACQ_IConstraint c, ACQ_Network learned, Chrono chrono) {
		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(toSmtlib(learned));
			myWriter.write("\n(assert" + c.getBwConstraint() + ")\n");
			myWriter.write("(check-sat)\n(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;
		chrono.start("explanation_solver_time_neg");

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		chrono.stop("explanation_solver_time_neg");

		Boolean sat = null;

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}

		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		return sat;
	}

	public Boolean solve(String exp, Map<String, String> regid, ArchType archtype, ACQ_Query q) {
		BufferedReader stdInput = null;
		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib2);
			//myWriter.write(toSmtlib(bk));
			//System.out.println(exp);
			myWriter.write(exp);
			myWriter.write(ptr_bk(cells, archtype, regid, q));
			myWriter.write("(check-sat)\n(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;

		String s;
		String s2 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		//System.out.println("RETURNED SOL \n"+s2);
		if(sat==null) {
			System.out.println(temp.getAbsolutePath());
		}
		return sat;
	}
	
	
	@Override
	public ACQ_Query solveAnyBlock(ACQ_Scope variable) {
		fireSolverEvent("BEG_solveQ", false, true);
		BitwuzlaAnswer answer = callBlock(variable);
		fireSolverEvent("END_solveQ", true, false);
		return answer.query;
	}

	private BitwuzlaAnswer callBlock(ACQ_Scope variable) {
		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(block_list);
			myWriter.write("\n(check-sat)\n" + "(get-model)\n" + "(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;
		Bitvec[] model = new Bitvec[acq_vars.size()];

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				} else if (s.contains("define-fun")) {
					Pattern p = Pattern.compile("\\(define-fun v(\\d+) \\(\\) \\(_ BitVec (\\d+)\\) #b([01]+)\\)");
					Matcher m = p.matcher(s.strip());
					if (m.matches()) {
						int varid = Integer.parseInt(m.group(1));
						Bitvec value = new Bitvec(new BigInteger(m.group(3), 2), Integer.parseInt(m.group(2)));
						model[varid] = value;
					}
				}
			}
			s = "";
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		if (sat) {
			block_model(model);
			return new BitwuzlaAnswer(sat, new ACQ_Query(variable, model));
		} else {
			return new BitwuzlaAnswer(sat, new ACQ_Query());
		}
	
	}

	private BitwuzlaAnswer call(ACQ_Scope variable) {
		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write("\n(check-sat)\n" + "(get-model)\n" + "(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;
		Bitvec[] model = new Bitvec[acq_vars.size()];

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				} else if (s.contains("define-fun")) {
					Pattern p = Pattern.compile("\\(define-fun v(\\d+) \\(\\) \\(_ BitVec (\\d+)\\) #b([01]+)\\)");
					Matcher m = p.matcher(s.strip());
					if (m.matches()) {
						int varid = Integer.parseInt(m.group(1));
						Bitvec value = new Bitvec(new BigInteger(m.group(3), 2), Integer.parseInt(m.group(2)));
						model[varid] = value;
					}
				}
			}
			s = "";
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		if (sat) {
			return new BitwuzlaAnswer(sat, new ACQ_Query(variable, model));
		} else {
			return new BitwuzlaAnswer(sat, new ACQ_Query());
		}
	}

	public ACQ_Query solveEnum(Explanation exp, String mss_block, ACQ_Query q, ArchType archtype, ACQ_Network bk) {

	    // ---- Pattern for declare-fun lines in the INPUT smtlib (any x-prefixed var) ----
	    Pattern declPattern = Pattern.compile(
	        "\\(declare-fun (x[a-zA-Z0-9_]*!\\S+) \\(\\) \\(_ BitVec (\\d+)\\)\\)"
	    );

	    // ---- Pattern for define-fun lines in the SOLVER OUTPUT (model values) ----
	    // group(1) = cellId, group(2) = sub-number (null if plain x<cellid>),
	    // group(3) = BitVec size, group(4) = bits
	    Pattern modelPattern = Pattern.compile(
	        "\\(define-fun x(\\d+)(?:_(\\d+))?(?:!\\S+)? \\(\\) \\(_ BitVec (\\d+)\\) #b([01]+)\\)"
	    );

	    // Build the full SMT-LIB source we send to the solver
	    String smtlibSource = base_smtlib2
	            + exp.getExp()
	            + getdomains(cells, q, archtype, exp.getRegId())
	            + ptr_bk(cells, archtype, exp.getRegId(), q)
	            + toSmtlib3(bk, q, exp.getRegId())
	            + mss_block
	            + "\n(check-sat)\n(get-model)\n(exit)";

	    // (Optional) collect declared x-variables from the input, useful for debugging/validation
	    List<String> xVars = new ArrayList<>();
	    Matcher mDecl = declPattern.matcher(smtlibSource);
	    while (mDecl.find()) {
	        xVars.add(mDecl.group(1));
	    }

	    File temp = null;
	    try {
	        temp = File.createTempFile("bitwuzla_", ".txt");
	        try (FileWriter myWriter = new FileWriter(temp)) {
	            myWriter.write(smtlibSource);
	        }
	    } catch (IOException e) {
	        e.printStackTrace();
	        return null;
	    }
	    assert temp != null : "temp file should not be null";

	    StringBuilder stdInputBuffer = new StringBuilder();
	    StringBuilder stdErrBuffer = new StringBuilder();

	    try {
	        String[] torun = new String[] {
	            String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")),
	            "-m",
	            temp.getPath()
	        };

	        Process proc = runtime.exec(torun);

	        try (BufferedReader stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
	             BufferedReader stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()))) {

	            String line;
	            while ((line = stdInput.readLine()) != null) {
	                stdInputBuffer.append(line).append("\n");
	            }
	            while ((line = stdErr.readLine()) != null) {
	                stdErrBuffer.append(line).append("\n");
	            }
	        }

	        proc.waitFor();
	    } catch (IOException | InterruptedException e1) {
	        e1.printStackTrace();
	        return null;
	    }

	    String fullOutput = stdInputBuffer.toString();
	    Boolean sat = null;

	    if (fullOutput.contains("unsat")) {
	        sat = false;
	    }
	    else if (fullOutput.contains("sat")) {
	        sat = true;
	    }

	    assert sat!=null;
	    if (!sat) {
	        //System.err.println("Solver failed or UNSAT. Errors:\n" + stdErrBuffer.toString());
	        return null;
	    }

	    // ---- Parse model values from solver output ----
	    Map<Integer, Bitvec> plainValues = new HashMap<>();                 // cellId -> value
	    Map<Integer, TreeMap<Integer, Bitvec>> refCandidates = new HashMap<>(); // cellId -> {number -> value}

	    Matcher mModel = modelPattern.matcher(fullOutput);
	    while (mModel.find()) {
	        int cellId = Integer.parseInt(mModel.group(1));
	        String subStr = mModel.group(2);
	        int size = Integer.parseInt(mModel.group(3));
	        BigInteger bits = new BigInteger(mModel.group(4), 2);
	        Bitvec value = new Bitvec(bits, size);

	        if (subStr == null) {
	            plainValues.put(cellId, value);
	        } else {
	            int number = Integer.parseInt(subStr);
	            refCandidates
	                .computeIfAbsent(cellId, k -> new TreeMap<>())
	                .put(number, value);
	        }
	    }

	    // ---- Resolve into model[] by walking cells ----
	    Bitvec[] model = new Bitvec[acq_vars.size()];

	    for (ACQ_CellVariable cell : cells) {
	        int cellId = cell.cellid;

	        // plain value
	        Bitvec value = plainValues.get(cellId);
	        if (value != null && cell.getValue() != null) {
	            model[cell.getValue().id] = value;
	        }

	        // copy size value directly from the incoming query q
	        if (cell.getSize() != null) {
	            model[cell.getSize().id] = q.getValue(cell.getSize().id);
	        }
	        if (cell.getRef() != null) {
	            model[cell.getRef().id] = q.getValue(cell.getRef().id);
	        }
	    }


	    return new ACQ_Query(q.scope, model);
	}
	private String getdomains(ACQ_CellVariable[] cells2, ACQ_Query q, ArchType archtype, Map<String, String> regid) {
		String res="";
		for (ACQ_CellVariable cell : cells) {
			int type_sz = cell.getType().getSize(archtype);
			// TODO put arch_size
			switch (cell.getType()) {
			case STR:
				res += String.format("(assert %s)\n", cell.getValueBwDomainBinsec(regid));
				
				break;

			case PTR:
			case INT:
			case INT8:
			case UINT:
			case UINT8:
			case UINT16:
			case BOOL:
				res += String.format("(assert %s)\n", cell.getValueBwDomainBinsec(regid));
				break;
			default:
				assert false;

			}
		}
		return res;
	}
	
	@Override
	public ACQ_Query solveQ2(ACQ_Network learned_network, ACQ_Network known_constraint) {
		fireSolverEvent("BEG_solveQ", false, true);
		BitwuzlaAnswer answer = call2(learned_network, known_constraint);
		fireSolverEvent("END_solveQ", true, false);
		return answer.query;

	}
	
	private BitwuzlaAnswer call2(ACQ_Network net, ACQ_Network known_constraint) {
		BufferedReader stdInput = null;
		BufferedReader stdErr = null;

		FileWriter myWriter;
		File temp = null;
		try {
			temp = File.createTempFile("bitwuzla_", ".txt");
			myWriter = new FileWriter(temp);
			// System.out.println("THE NETWORK \n" +net.toString());
			// System.out.println("CONTENT FOR SOLVER : \n"+toSmtlib(net));
			myWriter.write(base_smtlib);
			myWriter.write(toSmtlib(net));
			myWriter.write(toSmtlib(known_constraint));
			myWriter.write("\n(check-sat)\n" + "(get-model)\n" + "(exit)");
			myWriter.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		assert temp != null : "temp file should not be null";

		Process proc;

		try {
			String[] torun = new String[] { String.format("%s/resources/bitwuzla", System.getenv("PRECA_PATH")), "-m",
					// "-t" , String.format("%l", getLimit()),
					temp.getPath(), };

			proc = runtime.exec(torun);
			proc.waitFor();

			stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));
			stdErr = new BufferedReader(new InputStreamReader(proc.getErrorStream()));

			Files.deleteIfExists(temp.toPath());
		} catch (IOException | InterruptedException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		Boolean sat = null;
		Bitvec[] model = new Bitvec[acq_vars.size()];

		String s;
		String s2 = "";
		String s3 = "";

		try {
			while ((s = stdInput.readLine()) != null) {
				s2 = s2 + "\n" + s;

				if (s.contains("unsat")) {
					sat = false;
				} else if (s.contains("unknown")) {
					assert false;
				} else if (s.contains("sat")) {
					sat = true;
				} else if (s.contains("define-fun")) {
					Pattern p = Pattern.compile("\\(define-fun v(\\d+) \\(\\) \\(_ BitVec (\\d+)\\) #b([01]+)\\)");
					Matcher m = p.matcher(s.strip());
					if (m.matches()) {
						int varid = Integer.parseInt(m.group(1));
						Bitvec value = new Bitvec(new BigInteger(m.group(3), 2), Integer.parseInt(m.group(2)));
						model[varid] = value;
					}
				}
			}
			s = "";
			while ((s = stdErr.readLine()) != null) {
				s3 = s3 + "\n" + s;
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		// System.out.println("RETURNED SOL \n"+s2);
		assert sat != null : s3;
		if (sat) {
			return new BitwuzlaAnswer(sat, new ACQ_Query(net.getVariables(), model));
		} else {
			return new BitwuzlaAnswer(sat, new ACQ_Query());
		}
	}


}