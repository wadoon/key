package de.tud.cs.se.ds.psec.parser.ast;

import java.util.ArrayList;
import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Models a set of instructions.
 *
 * @author Dominic Scheurer
 */
public class Instructions extends TranslationTacletASTElement {

    private ArrayList<Instruction> instructions;

    /**
     * @param instructions
     *            The list of instructions.
     */
    public Instructions(ArrayList<Instruction> instructions) {
        this.instructions = instructions;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            final TacletApp app, List<TacletASTNode> children) {
        instructions.forEach(i ->
            i.translate(mv, pvHelper, app, children));
    }

}
