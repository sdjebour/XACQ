package io.github.binsec.core.combinatorial;

import java.util.Iterator;

import io.github.binsec.core.acqconstraint.ACQ_IConstraint;
import io.github.binsec.core.acqconstraint.ACQ_Network;
import io.github.binsec.core.acqconstraint.OverlapConstraint;
import io.github.binsec.core.acqconstraint.StrlenEqConstraint;
import io.github.binsec.core.learner.ACQ_Scope;
import io.github.binsec.core.learner.Answer;

public class SubMSSIterator implements Iterator<ACQ_Network> {

    public enum Strategy {
        LINEAR,
        COMPLEMENT,
        MIX,
        QUICKEXPLAIN
    }

    private final ACQ_Network elements;
    private final int maxLevel;
    private final Strategy strategy;

    private int[] indices;
    private int currentSize;
    private boolean done;
    private ACQ_Network lastSubset;
    private ACQ_Network lastWorkingPool = null;
    private ACQ_Network currentPool;
    private boolean levelExhausted;
    CombinationIterator combIter;
    Answer ans;


    public SubMSSIterator(ACQ_Network elements, int maxLevel, Strategy strategy) {
        this.elements = elements;
        this.maxLevel = Math.min(maxLevel, elements.size());
        this.done = false;
        this.levelExhausted = false;
        /*if(strategy==Strategy.MIX) {
        	if(ans==Answer.NO) this.strategy=Strategy.LINEAR;
        	else this.strategy=Strategy.COMPLEMENT;
        }
        else {
        	this.strategy=strategy;
        }
        switch (this.strategy) {
            case LINEAR:
                currentSize = 1;
                break;
            case COMPLEMENT:
                currentSize = elements.size() - maxLevel;
                break;
        }*/
        this.strategy=strategy;
        combIter = new CombinationIterator(elements.size(), currentSize);
        currentPool=buildValidSubset();

        
    }

    @Override
    public boolean hasNext() {
        return !done;
    }

    @Override
    public ACQ_Network next() {
    	ACQ_Network res = new ACQ_Network(currentPool);
    	currentPool= buildValidSubset();
    	return res;
        
    }

    public void feedback(boolean worked) {
        
    }
  

    protected boolean isValidSubset(ACQ_Network subset) {
        for (ACQ_IConstraint c : subset) {
            if (c instanceof OverlapConstraint) {
                int nb_found = 0;
                ACQ_Scope scope = c.getScope();
                for (ACQ_IConstraint other : subset) {
                    if (other instanceof StrlenEqConstraint) {
                        if (scope.containsAll(other.getScope())) {
                            nb_found++;
                        }
                    }
                }
                if (nb_found != 2) return false;
            }
        }
        return true;
    }

    private ACQ_Network buildValidSubset() {
        
    	while (true) {
            if (combIter.hasNext()) {
                int[] indices = combIter.next();
                ACQ_Network subset = buildSubset(indices);
                if (isValidSubset(subset)) {
                    return subset;
                }
               
            } else {
                
                currentSize++;
                if (strategy == Strategy.LINEAR && currentSize > maxLevel) {
                    done = true;
                    return null;
                }
                if (strategy == Strategy.COMPLEMENT && currentSize >= elements.size()) {
                    done = true;
                    return null;
                }
                combIter = new CombinationIterator(elements.size(), currentSize);
            }
        }
    }
    
    private ACQ_Network buildSubset(int[] indices) {
        ACQ_Network subset = new ACQ_Network(elements.getFactory(), elements.getVariables());
        for (int i : indices) {
            subset.add(elements.getConstraints().get_Constraint(i), true);
        }
        return subset;
    }

    public ACQ_Network getLastWorkingPool() {
        return lastWorkingPool;
    }

    public boolean isLevelExhausted() {
        return levelExhausted;
    }
}
   
