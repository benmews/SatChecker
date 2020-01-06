import java.io.IOException;
import java.io.BufferedReader;
import java.io.FileReader;
import java.util.ArrayList;

class Solver {

	public ArrayList<ArrayList<Integer>> parse_dimacs(String filename) throws IOException {
		
		ArrayList<ArrayList<Integer>> clauses = new ArrayList<ArrayList<Integer>>();
		BufferedReader br = new BufferedReader(new FileReader(filename));
		
		String line;
		while ((line = br.readLine()) != null) {
			line = line.trim();
			if (line.startsWith("c")) continue;
			if (line.startsWith("p")) continue;
			ArrayList<Integer> clause = new ArrayList<Integer>();
			for (String literal: line.split("\\s+")) {
				Integer lit = new Integer(literal);
				if (lit == 0) break;
				clause.add(lit);
			}
			if (clause.size() > 0) {
				clauses.add(clause);
			}
		}
		return clauses;
	}

	public static void main(String[] args) throws IOException {
		Solver solver = new Solver();
		ArrayList<ArrayList<Integer>> clauses = solver.parse_dimacs(args[0]);
		System.out.println(clauses);
	}
	
}