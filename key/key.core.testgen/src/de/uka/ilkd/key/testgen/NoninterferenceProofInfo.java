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

/**
 * this class provides proof information for noninterference-proofs
 * (e.g. postcondition from noninterference-proofs,
 * both code parts from noninterference-proofs)
 * @author Muessig
 *
 */
public class NoninterferenceProofInfo extends ProofInfo {

    /**
     * Constructor for the class {@link NoninterferenceProofInfo}
     * @param proof The current {@link Proof}
     */
    public NoninterferenceProofInfo(Proof proof) {
        super(proof);
    }

    /**
     * returns the postcondition for a noninterference proof
     * @return the postcondition as {@link Term}
     */
    @Override
    public Term getPostCondition() {

        Term t = getPO();
        Term post = services.getTermBuilder().tt();
        try {
            post = t.sub(1);
            if (post.op() == Junctor.IMP) {
                post = post.sub(1);
            }
        } catch (Exception e) {
            System.err.println("Could not get PostCondition");
        }
        return post;
    }

    @Override
    public String getCode() {
        String[] result = getCodeNoninterference();
        String r = "";
        for (String code : result) {
            r = r + code + TestCaseGenerator.NEW_LINE;
        }
        return r;
    }

    /**
     * This method returns the two java code blocks from noninterference-proofs
     * @return String array with two java code blocks
     * @author Muessig
     */
    public String[] getCodeNoninterference() {
        Term f = getPO();
        String[] result = new String[2];
        List<JavaBlock> blocks = getJavaBlocks(f);

        List<Term> terme1 = new ArrayList<>();
        List<Term> terme2 = new ArrayList<>();
        for (Term s : f.subs()) {
            if (s.containsJavaBlockRecursive()) {
                terme1.add(s);
            }
        }
        // collect the two terms which contains a java block for updates
        for (Term s : terme1) {
            for (Term a : s.subs()) {
                if (a.containsJavaBlockRecursive()) {
                    terme2.add(a);
                }
            }
        }
        if (blocks.size() > 2) {
            System.out.println("Warning: more than 2 JavaBlocks found!");
        }

        for (int i = 0; i < result.length; i++) {
            try {
                StringWriter sw = new StringWriter();
                PrettyPrinter pw = new CustomPrettyPrinter(sw, false);
                sw.write("    " + getUpdate(terme2.get(i)) + "\n");
                blocks.get(i).program().prettyPrint(pw);
                result[i] = sw.getBuffer().toString();

            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return result;
    }

    /**
     * returns the {@link JavaBlock}s in the Term
     * @param term The {@link Term} you want the {@link JavaBlock}s from.
     * @return An {@link ArrayList} with {@link JavaBlock}s which are contained
     * in the given {@link Term} term. The {@link ArrayList} is empty if term does not contain
     * {@link JavaBlock}s.
     */
    public List<JavaBlock> getJavaBlocks(Term term) {
        List<JavaBlock> blocks = new ArrayList<JavaBlock>();
        getJavaBlocksHelp(term, blocks);
        return blocks;
    }

    private void getJavaBlocksHelp(Term f, List<JavaBlock> blocks) {

        if (f.containsJavaBlockRecursive()) {
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

    //TODO check if we can use the getUpdate method from super class
    @Override
    public String getUpdate(Term t) { // maybe without recursion
        String result = "";
        if (t.containsJavaBlockRecursive()) {
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
