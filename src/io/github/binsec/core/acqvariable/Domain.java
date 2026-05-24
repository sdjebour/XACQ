package io.github.binsec.core.acqvariable;

import java.util.ArrayList;
import java.util.Random;

import io.github.binsec.core.tools.ArchType;

public class Domain {

	CellType type;
	ArchType arch;
	int lower;
	int upper;
	
	ArrayList<Integer> added_values = new ArrayList<Integer>();
	
	public Domain(CellType t, ArchType ar) {
		type = t;
		arch = ar;
	}
	
	public void update_lower(int v) {
		// lower included
		lower = v;
	}
	
	public void update_upper(int v) {
		// upper included
		upper = v;
	}
	
	public void add_value(int v) {
		if (!added_values.contains(v)) {
			added_values.add(v);
		}
	}
	
	public int rand() {
		int number_elems = added_values.size() + (upper - lower + 1);
		Random random = new Random();
		int index = random.nextInt(number_elems);
		if (index < added_values.size()) {
			return added_values.get(index);
		}
		else {
			index -= added_values.size();
			return lower + index;
		}
	}
	
	private String toBw(int v) {
		int size = type.getSize(arch) / 4;
		String fmt = "#x%0" + size + "x";
		if(type==CellType.INT8||type==CellType.UINT8) return String.format(fmt, v& 0xFF);
		return String.format(fmt, v);
	}
	
	public String getBwDomain(String var) {
		String added_vals_res = added_values.size() > 1  ? "(or" : ""; // If only one value, no need for the or
		for (int v : added_values)
			added_vals_res += String.format(" (= %s %s)", var, toBw(v));
		added_vals_res += added_values.size() > 1 ? ")" : "";
		
		String interval_res;
		switch (type) {
		case INT:
		case INT8:
			interval_res = String.format("(and (bvsge %s %s) (bvsle %s %s))", var, toBw(lower), var, toBw(upper));
			break;
			
		case PTR:
		case STR:
		case UINT:
		case UINT16:
		case UINT8:
			if (lower == 0) interval_res = String.format("(bvule %s %s)", var, toBw(upper));
			else interval_res = String.format("(and (bvuge %s %s) (bvule %s %s))", var, toBw(lower), var, toBw(upper));
			break;
			
		case BOOL:
			interval_res = String.format("(and (bvuge %s %s) (bvule %s %s))", var, toBw(lower), var, toBw(upper));
			break;
		default:
			assert false : "Unknown type";
			return null;
		}
		
		if (added_values.size() > 0) return String.format("(or %s %s)", interval_res, added_vals_res);
		else return interval_res;
	}
}
