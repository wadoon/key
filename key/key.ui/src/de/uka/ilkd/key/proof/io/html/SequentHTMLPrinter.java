package de.uka.ilkd.key.proof.io.html;

import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;

import java.io.StringWriter;

import static de.uka.ilkd.key.proof.io.html.Section.*;

/**
 * Created by weigl on 3/24/16.
 */
public class SequentHTMLPrinter implements Visitor {

    private final HTMLCodeWriter writer = new HTMLCodeWriter();
    private final Sequent sequent;

    public SequentHTMLPrinter(Sequent sequent) {
        this.sequent = sequent;
    }


    private String print() {
        {
            writer.div(SEQUENT);

            writer.div(ANTECEDENT);
            print(sequent.antecedent());
            writer.end();

            writer.div(SUCCEDENT);
            print(sequent.succedent());
            writer.end();

            writer.end();
        }
        return writer.toString();
    }

    private void print(Semisequent ss) {
        for (SequentFormula sf : ss.asList()) {
            writer.div(SEQUENT_FORMULA);
            //print(sf);
            writer.append(
                    LogicPrinter.quickPrintSemisequent(ss, null)
            );
            writer.end();
        }
    }

    private void print(SequentFormula sf) {
        print(sf.formula());
    }

    private void print(Term formula) {
        boolean rigid = formula.isRigid();
        boolean containsRecursive = formula.isContainsJavaBlockRecursive();

        writer.span(TERM, rigid ? RIGID : EMPTY, containsRecursive ? RECURSIVE_JAVA_BLOCK : EMPTY);
        writer.span(formula.getLabels());

        StringWriter sw = new StringWriter();
        ProgramPrinter pp = new ProgramPrinter(sw);
        //LogicPrinter lp = new LogicPrinter(pp, new NotationInfo(), new Services(Profile));
        /*
        JavaBlock javaBlock = formula.javaBlock();
        if (!javaBlock.isEmpty()) {
            if (formula.op() == Modality.DIA) {
                writer.append("\\<");
                print(javaBlock);
                writer.append("\\> ");
            } else if (formula.op() == Modality.BOX) {
                writer.append("\\[");
                print(javaBlock);
                writer.append("\\] ");
            } else {
                writer.append(formula.op()).append("\\[").append(javaBlock).append("\\] ");
            }
            writer.append("(");
            print(formula.sub(0));
            writer.append(")");
        } else {
            Notation n = ni.getNotation(formula.op());
            if (!formula.boundVars().isEmpty()) {
                writer.append("{");
                for (int i = 0, n = formula.boundVars().size(); i < n; i++) {
                    writer.append(formula.boundVars().get(i));
                    if (i < n - 1) {
                        writer.seperator(", ");
                    }
                }
                writer.append("}");
            }

            if (formula.arity() != 0) {
                writer.append("(");
                for (int i = 0, ar = formula.arity(); i < ar; i++) {
                    print(formula.sub(i));
                    if (i < ar - 1) {
                        writer.seperator(",");
                    }
                }
                writer.append(")");
            }
        }
        */

        writer.end();
        writer.end();
    }

    private void print(JavaBlock javaBlock) {
        writer.append(javaBlock.program());
    }


    public static String print(Sequent sequent) {
        return new SequentHTMLPrinter(sequent).print();
    }

    @Override
    public boolean visitSubtree(Term visited) {
        return true;
    }

    @Override
    public void visit(Term visited) {

    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {

    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {
        writer.append(subtreeRoot.op());
    }
}
