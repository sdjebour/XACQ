package io.github.binsec.core.acqsolver;

import io.github.binsec.core.learner.ACQ_Query;

public class BitwuzlaAnswer {
	
	public Boolean sat = null;
	public ACQ_Query query = null;
	
	public BitwuzlaAnswer(boolean sat, ACQ_Query model) {
		this.sat = sat;
		this.query = model;
	}
	public BitwuzlaAnswer(boolean sat) {
		this.sat = sat;
	}
	
	
	public ACQ_Query getQuery() {
		//System.out.println(query.toString2());
		return query;
	}
	
	public Boolean isSat() {
		return this.sat;
	}
	
}
