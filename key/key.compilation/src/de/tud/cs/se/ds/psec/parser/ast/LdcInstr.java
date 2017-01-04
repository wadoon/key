package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.GlobalLabelHelper;
import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * A bytecode LDC instruction.
 *
 * @author Dominic Scheurer
 */
public class LdcInstr extends Instruction {
    private String locVarSV;

    /**
     * @param insn
     *            The bytecode instruction.
     * @param locVarSV
     *            The location variable that is the argument of this
     *            {@link LdcInstr}.
     */
    public LdcInstr(String locVarSV) {
        this.locVarSV = locVarSV;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            GlobalLabelHelper globalLabelHelper, UniqueLabelManager labelManager,
            RuleInstantiations instantiations, Services services, List<TacletASTNode> children) {

        String strWithQuotes = instantiations.getInstantiationFor(locVarSV).get().toString();
        mv.visitLdcInsn(strWithQuotes.substring(1, strWithQuotes.length() - 1));

    }

}
