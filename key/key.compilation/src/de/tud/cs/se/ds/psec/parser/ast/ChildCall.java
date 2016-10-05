package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Request for the translation of the children in the taclet AST.
 *
 * @author Dominic Scheurer
 */
public class ChildCall extends Instruction {

    private int childNo;

    /**
     * Constructs a new {@link ChildCall} to the child in the taclet AST with
     * the given number.
     * 
     * @param childNo
     *            The numer of the child to be compiled.
     */
    public ChildCall(int childNo) {
        this.childNo = childNo;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, TacletApp app, Services services,
            List<TacletASTNode> children) {
        // XXX Remove this hack!!!
        if (children.size() > childNo - 1) {
            children.get(childNo - 1).compile();
        }
    }

}
