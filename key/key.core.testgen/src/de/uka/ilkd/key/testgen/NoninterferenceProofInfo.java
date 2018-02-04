package de.uka.ilkd.key.testgen;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Proof;

public class NoninterferenceProofInfo extends ProofInfo {

	
	
	public NoninterferenceProofInfo(Proof proof) {
		super(proof);
	}

	/**
	 * returns the Post condition for a noninterference contract
	 * @return the postcondition term
	 */
	@Override
	public Term getPostCondition() {//TODO maybe new class with dynamic binding 
		
		Term t = getPO();
		Term post = services.getTermBuilder().tt();
		try{
			post = t.sub(1);
			if(post.op() == Junctor.IMP) {
				post = post.sub(1);
			}
		}catch(Exception e){
			System.err.println("Could not get PostCondition");
		}
		return post;
	}
	
	/**
	 * This method returns you the two java blocks for 
	 * information flow tests (two java blocks for two MUT-executions)
	 * @return String array with two java blocks
	 * @author Muessig
	 */
	@Override
	public String getCode() {//TODO return value String 
		Term f = getPO();
		String[] result = new String[2];
		List<JavaBlock> blocks = getJavaBlocks(f);
		
		if(blocks.size() > 2) {
			System.out.println("Warning: more than 2 JavaBlocks, "
					+ "check if the MUT calls are correct");
		}
		
		for (int i = 0; i < result.length; i++) {
			try {

				StringWriter sw = new StringWriter();

				PrettyPrinter pw = new CustomPrettyPrinter(sw,false);

				if (i == 0) {
					sw.write("   "+getUpdate(f)+"\n");
				}

				blocks.get(i).program().prettyPrint(pw);
				result[i] = sw.getBuffer().toString();

			} catch (IOException e) {	       
				e.printStackTrace();
			}
		}
		String r = "";
		for (String code : result) {
			r = r + code + TestCaseGenerator.NEW_LINE;
		}
		return r;

	}
	
	public List<JavaBlock> getJavaBlocks(Term f) { //TODO muessig check if needed
		List<JavaBlock> blocks = new ArrayList<JavaBlock>();
		getJavaBlocksHelp(f, blocks);
		return blocks;
	}
	
	private void getJavaBlocksHelp(Term f, List<JavaBlock> blocks) {
		
		if(f.containsJavaBlockRecursive()) {
			for (Term s : f.subs()) {
				if (s.containsJavaBlockRecursive()) {
					if (!s.javaBlock().isEmpty()) {
						blocks.add(s.javaBlock());
					}	
					getJavaBlocksHelp(s, blocks);
				}
			}
		}
	}
	
	@Override
	public String getUpdate(Term t) { // maybe without recursion 
		
		String result = "";
		if(t.containsJavaBlockRecursive()) {
			for (Term s : t.subs()) {
				if (s.containsJavaBlockRecursive()) {
					if (!s.javaBlock().isEmpty()) {
						result = result + super.getUpdate(t);
					}	
					result = result + getUpdate(s);
				}
			}
		}
		
		return result;
		
	}
}
