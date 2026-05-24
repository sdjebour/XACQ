package io.github.binsec.core.basics;

import java.math.BigInteger;

public class Bitvec {
	
	BigInteger unsigned;
	public int size;
	BigInteger slimit;
	BigInteger ulimit;
	BigInteger umask;
	
	public Bitvec(BigInteger val, int size) {
		assert size <= 64;
		assert size % 2 == 0;
		this.size = size;
		ulimit = BigInteger.ONE.shiftLeft(size);
		slimit = BigInteger.ONE.shiftLeft(size-1);
		umask = ulimit.subtract(BigInteger.ONE);
		
		if (val.compareTo(BigInteger.ZERO) < 0) unsigned = val.add(ulimit);
		else unsigned = val;
	}
	
	public BigInteger unsigned() {
		return unsigned.and(umask);
	}
	
	public BigInteger signed() {
		if (unsigned.compareTo(slimit) >= 0) {
			return unsigned.subtract(ulimit);
		}
		else {
			return unsigned;
		}
	}
	
	public int scompareTo(Bitvec bv) {
		//assert size == bv.size;
		BigInteger v1 = signed();
		BigInteger v2 = bv.signed();
		return v1.compareTo(v2);
	}
	
	public int ucompareTo(Bitvec bv) {
		//assert size == bv.size;
		BigInteger v1 = unsigned();
		BigInteger v2 = bv.unsigned();
		return v1.compareTo(v2);
	}
	
	public Bitvec add(Bitvec bv) {
		if (this.size == bv.size) {
	        return new Bitvec(this.unsigned.add(bv.unsigned), size);
	    }

	    int targetSize = Math.max(this.size, bv.size);

	    Bitvec v1;
	    Bitvec v2;

	    
	        v1 = new Bitvec(this.unsigned,targetSize);
	    
	        v2 = new Bitvec(bv.unsigned,targetSize);
	    

	    return new Bitvec(v1.add(v2).unsigned, targetSize);
	}
	
	public Bitvec subtract(Bitvec bv) {
		
		if (this.size == bv.size) {
	        return new Bitvec(this.unsigned.subtract(bv.unsigned), size);
	    }

	    int targetSize = Math.max(this.size, bv.size);

	    Bitvec v1;
	    Bitvec v2;

	    
	        v1 = new Bitvec(this.unsigned,targetSize);
	    
	        v2 = new Bitvec(bv.unsigned,targetSize);
	    

	    return new Bitvec(v1.subtract(v2).unsigned, targetSize);
	}
	
	public Bitvec multiply(Bitvec bv) {
		if (this.size == bv.size) {
	        return new Bitvec(this.unsigned.multiply(bv.unsigned), size);
	    }

	    int targetSize = Math.max(this.size, bv.size);

	    Bitvec v1;
	    Bitvec v2;

	    
	        v1 = new Bitvec(this.unsigned,targetSize);
	    
	        v2 = new Bitvec(bv.unsigned,targetSize);
	    

	    return new Bitvec(v1.multiply(v2).unsigned, targetSize);
	}
	
	public Bitvec mod(Bitvec bv) {

	    int targetSize = Math.max(this.size, bv.size);

	    Bitvec v1;
	    Bitvec v2;

	    
	        v1 = new Bitvec(this.unsigned,targetSize);
	    
	        v2 = new Bitvec(bv.unsigned,targetSize);
	    

	   return new Bitvec(v1.unsigned.mod(v2.unsigned), targetSize);
	}
	
	public Bitvec abs() {
		if (unsigned.compareTo(slimit) >= 0) {
			BigInteger abs = unsigned.subtract(ulimit).negate();
			return new Bitvec(abs, size);
		}
		else {
			return this;
		}
	}
	
	public Bitvec[] divideAndRemainder(Bitvec bv) {
		
		if (this.size == bv.size) {
			BigInteger[] divrem = unsigned.divideAndRemainder(bv.unsigned);
			return new Bitvec[] {new Bitvec(divrem[0], size), new Bitvec(divrem[1], size) };
	    }

	    int targetSize = Math.max(this.size, bv.size);

	    Bitvec v1;
	    Bitvec v2;

	    
	        v1 = new Bitvec(this.unsigned,targetSize);
	    
	        v2 = new Bitvec(bv.unsigned,targetSize);
			BigInteger[] divrem = v1.unsigned.divideAndRemainder(v2.unsigned);

	    
			return new Bitvec[] {new Bitvec(divrem[0], targetSize), new Bitvec(divrem[1], targetSize)};
	}
	
	public static Bitvec one(int size) {
		return new Bitvec(BigInteger.ONE, size);
	}
	
	public static Bitvec zero(int size) {
		return new Bitvec(BigInteger.ZERO, size);
	}
	

	public boolean equals(Bitvec bv) {
		
		 int targetSize = Math.max(this.size, bv.size);

		    Bitvec v1;
		    Bitvec v2;

		    
		        v1 = new Bitvec(this.unsigned,targetSize);
		    
		        v2 = new Bitvec(bv.unsigned,targetSize);
		    

		    return v1.unsigned().equals(v2.unsigned());
		
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + unsigned.hashCode();
		result = prime * result + size;
		
		return result;
	}

	@Override
	public boolean equals(Object obj) {

		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Bitvec other = (Bitvec) obj;
		if (!this.unsigned.equals(other.unsigned)) {
			return false;
		}
		if (this.size != other.size) {
			return false;
		}

		return true;
	}
	
	public boolean equals(int obj) {
		Bitvec other = new Bitvec(new BigInteger(Integer.toString(obj)),this.size);
		if (!this.unsigned.equals(other.unsigned)) {
			return false;
		}
		return true;
	}
}
