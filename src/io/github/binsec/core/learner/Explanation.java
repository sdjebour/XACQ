package io.github.binsec.core.learner;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import io.github.binsec.core.acqvariable.ACQ_CellVariable;
import io.github.binsec.core.acqvariable.CellType;

public class Explanation {
	
	String formula;
	Map<String, String> regid;
	String memory;
	
	public Explanation(String formula){
		this.formula=formula;
	}
	
	public Explanation(String formula, Map<String, String> regid){
		this.formula=formula;
		this.regid=regid;
	}
	
	public Explanation(){
		this.formula=null;
	}
	
	public void setExp(String formula){
		this.formula=formula;
	}
	
	public String getExp() {
		return this.formula;
	}

	public void getFormulaBinsecOutput(String output, ACQ_CellVariable[] cells,ACQ_Query q) {
	    String[] lines = output.split("\\R"); // \R splits on any line break
	    StringBuilder result = new StringBuilder();

	    Pattern arrayDef = Pattern.compile("^\\(define-fun\\s+(\\S+)\\s+\\(\\)\\s+\\(Array");

	    boolean inSection = false;
	    boolean firstBlockFinished = false;
	    boolean insideFirstBlock = false;

	    String previousMemory = null;

	    for (String line : lines) {

	        // Enter main section
	        if (line.startsWith("[sse:result] Formula")) {
	            inSection = true;
	            continue;
	        }

	        // End of section
	        if (line.startsWith("[sse:info]") && inSection) {
	            break;
	        }

	        if (!inSection) continue;

	        String trimmed = line.trim();
	        if (trimmed.contains("exit")) {
	            trimmed = trimmed.replace("exit", "exit2");
	        }
	        result.append(trimmed).append(System.lineSeparator());

	        // If the first block is already finished ignore array defs entirely
	        if (firstBlockFinished) continue;

	        Matcher m = arrayDef.matcher(trimmed);

	        if (m.find()) {
	            insideFirstBlock = true;

	            // save previous memory
	            previousMemory = this.memory;

	            // set new memory
	            this.memory = m.group(1);

	            // rollback if this definition involves a select
	            if (trimmed.contains("(select")) {
	                this.memory = previousMemory;
	            }

	        } else {
	            // We encounter a non-array line
	            if (insideFirstBlock) {
	                firstBlockFinished = true;
	            }
	        }
	    }
	    //System.out.println("\n binsec output : \n" + output);
	    //System.out.println("LA FORMULE : " + result.toString());
	    //System.out.println("mem id : " + this.memory);

	    this.formula = "\n" + result.toString();
	}

	public void setRegId(Map<String, String> regid) {
		this.regid=regid;
	}
	
	public Map<String, String> getRegId() {
		return this.regid;
	}

	public String getMemId() {
		return memory;
	}

	public Explanation getNegation() {
		int firstAssert = this.getExp().indexOf("(assert");
        if (firstAssert == -1) {
            throw new IllegalArgumentException("Aucun (assert ...) trouvé");
        }

        String header = this.getExp().substring(0, firstAssert).trim();
        String assertsPart = this.getExp().substring(firstAssert);

        List<String> asserts = extractAsserts(assertsPart);

        if (asserts.isEmpty()) {
            throw new IllegalStateException("Aucune assertion extraite");
        }

        StringBuilder neg = new StringBuilder();
        if(asserts.size()>1) {
        neg.append("(assert (not (and\n");
        for (String a : asserts) {
            neg.append("  ").append(a).append("\n");
        }
        neg.append(")))");
        }
        else {
        	neg.append("(assert (not \n");
        	neg.append("  ").append(asserts.get(0)).append("\n");
        	neg.append("))");
        }

        return new Explanation(header + "\n\n" + neg.toString(),this.regid);
    }

    private static List<String> extractAsserts(String text) {
        List<String> asserts = new ArrayList<>();
        int i = 0;

        while (true) {
            int start = text.indexOf("(assert", i);
            if (start == -1) break;

            int pos = start + "(assert".length();

            // Skip whitespace
            while (pos < text.length() && Character.isWhitespace(text.charAt(pos))) {
                pos++;
            }

            int exprStart = pos;
            int exprEnd;

            if (text.charAt(pos) == '(') {
                // Case: parenthesized expression
                int depth = 0;
                for (int j = pos; j < text.length(); j++) {
                    char c = text.charAt(j);
                    if (c == '(') depth++;
                    else if (c == ')') depth--;

                    if (depth == 0) {
                        exprEnd = j;
                        asserts.add(text.substring(exprStart, exprEnd + 1).trim());
                        i = j + 1;
                        break;
                    }
                }
            } else {
                // Case: atomic symbol (e.g. !z)
                int j = pos;
                while (j < text.length()
                        && !Character.isWhitespace(text.charAt(j))
                        && text.charAt(j) != ')') {
                    j++;
                }
                exprEnd = j - 1;
                asserts.add(text.substring(exprStart, exprEnd + 1).trim());
                i = j;
            }
        }
        
        return asserts;

        
        
}
    
    public int countAssert() {
        int count = 0;
        int index = 0;

        while ((index = getExp().indexOf("assert", index)) != -1) {
            count++;
            index += "assert".length();
        }
        return count;
    }
}
