package io.github.binsec.core.acqsolver;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.basics.Bitvec;
import io.github.binsec.core.learner.ACQ_Query;
import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.tools.Chrono;

public class BitwuzlaModelIterator implements Iterator<BitwuzlaAnswer> {

    private String bwfile;
    private ArrayList<String> acq_vars = new ArrayList<>(); 
    private final int maxSolutions;
    private int currentCount = 0;
    private List<Map<String, String>> solutions = new ArrayList<>();
    
    
    protected BitwuzlaAnswer next;
    private boolean hasMoreSolutions = true;
	private ACQ_Scope scope;
	private Chrono chrono;

    public BitwuzlaModelIterator(String basefile, int maxSolutions, ArrayList<String> acq_vars, ACQ_Scope scope, ACQ_Query q, Chrono chrono) {
    	this.scope=scope;
    	this.bwfile = basefile+block_model(q);
        this.maxSolutions = maxSolutions;
        this.acq_vars=acq_vars;
        this.chrono=chrono;
        advance();
    }

   
    public String block_model(ACQ_Query q) {
		String res="";
		for(int i=0;i<scope.size();i++) {
			res=res+"(assert (not (= v"+i+" (_ bv"+scope.getProjection(q)[i].unsigned()+ " 32))))\n";
		}
		return res;
	}
    
    public String block_model(Bitvec[] model) {
		String res="";
		for(int i=0;i<model.length;i++) {
			res=res+"(assert (not (= v"+i+" (_ bv"+model[i].unsigned()+ " 32))))\n";
		}
		return res;
	}
    
    public String block_class(ACQ_Network n) {
    	
		String res="(or";
		for(int i=0;i<n.size();i++) {
			res=res+" ("+n.getConstraints().get_Constraint(i).getBwConstraint()+") ";
			
		}
		return res+")";
	}
    
    public BitwuzlaAnswer getNext() {
        return next;
    }
    
    private void advance() {
    	   
    	
		FileWriter myWriter;
		File temp = null;
	    try {
	    	temp = File.createTempFile("bitwuzla_", ".txt");
	    	myWriter = new FileWriter(temp);
			myWriter.write(bwfile);
			myWriter.write("\n(check-sat)\n"+ "(get-model)\n"+ "(exit)");
			myWriter.close();
	    } catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	    assert (temp != null && temp.exists()):"file was deleted?";
	    
    	try {
    	        String[] torun = new String[] {
    	            "/usr/local/bin/bitwuzla",
    	            "-m",
    	            temp.getAbsolutePath() 
    	        };
    	        chrono.start("explanation_solver_time");
    	        Process proc = Runtime.getRuntime().exec(torun);
    	        proc.waitFor();
    	        chrono.stop("explanation_solver_time");

    	        BufferedReader stdInput = new BufferedReader(
    	            new InputStreamReader(proc.getInputStream())
    	        );

    	        Boolean sat = null;
    	        Bitvec[] model = new Bitvec[acq_vars.size()];
    	        String s;

    	        while ((s = stdInput.readLine()) != null) {
    	            if (s.contains("unsat")) {
    	                sat = false;
    	            } else if (s.contains("unknown")) {
    	                throw new IllegalStateException("Bitwuzla returned 'unknown'");
    	            } else if (s.contains("sat")) {
    	                sat = true;
    	            } else if (s.contains("define-fun")) {
    	                Pattern p = Pattern.compile(
    	                    "\\(define-fun v(\\d+) \\(\\) \\(_ BitVec 32\\) #b([01]+)\\)"
    	                );
    	                Matcher m = p.matcher(s.strip());
    	                if (m.matches()) {
    	                    int varid = Integer.parseInt(m.group(1));
    	                    Bitvec value = new Bitvec(new BigInteger(m.group(2), 2), 32);
    	                    model[varid] = value;
    	                }
    	            }
    	        }
    	        assert sat!=null : "solver error when searching for random models";
    	        if (sat) {
    	            bwfile= bwfile+"\n"+block_model(model);
    	            
    	            currentCount++;
    	            next= new BitwuzlaAnswer(true, new ACQ_Query(scope, model));
    	        } else {
    	        	hasMoreSolutions=false;
    	        	 next= null;
    	        }

    	    } catch (IOException | InterruptedException e) {
    	        throw new RuntimeException("Bitwuzla execution failed", e);
    	    }
		
	}

	

	@Override
	public boolean hasNext() {
	    return hasMoreSolutions && currentCount < maxSolutions;
	}

	
	 @Override
	    public BitwuzlaAnswer next() {
	        if (next == null) {
	            return null;
	        }
	        BitwuzlaAnswer result = next;
	        advance();
	        return result;
	    }
}
