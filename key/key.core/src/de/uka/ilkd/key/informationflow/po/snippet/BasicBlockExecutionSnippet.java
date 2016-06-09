package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.speclang.BlockContract.Variables;


/**
 *
 * @author christoph
 */
class BasicBlockExecutionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public JavaDLTerm produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        ImmutableList<JavaDLTerm> posts = ImmutableSLList.<JavaDLTerm>nil();
        if (poVars.post.self != null) {
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));
        }
        Iterator<JavaDLTerm> localVars = d.origVars.localVars.iterator();
        Iterator<JavaDLTerm> localPostVars = poVars.post.localVars.iterator();
        while (localVars.hasNext()) {
            posts = posts.append(d.tb.equals(localPostVars.next(), localVars.next()));
        }
        if (poVars.post.result != null) {
            posts = posts.append(d.tb.equals(poVars.post.result,
                                             poVars.pre.result));
        }
        if (poVars.pre.exception != null && poVars.post.exception != null) {
            posts = posts.append(d.tb.equals(poVars.post.exception,
                                             poVars.pre.exception));
        }
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));
        final JavaDLTerm prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }

    private JavaDLTerm buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  JavaDLTerm postTerm,
                                  TermBuilder tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                                                    "program-term for a contract without modality.");
        }

        //create java block
        Modality modality =
                (Modality) d.get(BasicSnippetData.Key.MODALITY);
        final JavaBlock jb = buildJavaBlock(d, vs);

        //create program term
        final Modality symbExecMod;
        if (modality == Modality.BOX) {
            symbExecMod = Modality.DIA;
        } else {
            symbExecMod = Modality.BOX;
        }
        final JavaDLTerm programTerm = tb.prog(symbExecMod, jb, postTerm);

        //create update
        JavaDLTerm update = tb.skip();
        Iterator<JavaDLTerm> paramIt = vs.pre.localVars.iterator();
        Iterator<JavaDLTerm> origParamIt = d.origVars.localVars.iterator();
        while (paramIt.hasNext()) {
            JavaDLTerm paramUpdate =
                    d.tb.elementary(origParamIt.next(), paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }
        if (vs.post.self != null) {
            final JavaDLTerm selfTerm = (JavaDLTerm) d.get(BasicSnippetData.Key.BLOCK_SELF);
            final JavaDLTerm selfUpdate =
                    d.tb.elementary(selfTerm, vs.pre.self);
            update = tb.parallel(selfUpdate, update);
        }
        return tb.apply(update, programTerm);
    }


    private JavaBlock buildJavaBlock(BasicSnippetData d,
                                     ProofObligationVars poVars) {
        final ExecutionContext context =
                (ExecutionContext) d.get(BasicSnippetData.Key.EXECUTION_CONTEXT);
        final ProgramVariable exceptionParameter =
                poVars.exceptionParameter.op(ProgramVariable.class);

        //create block call
        final Label[] labelsArray = (Label[]) d.get(BasicSnippetData.Key.LABELS);
        final ImmutableArray<Label> labels = new ImmutableArray<Label>(labelsArray);
        final Variables variables = (Variables) d.get(BasicSnippetData.Key.BLOCK_VARS);
        final StatementBlock block = (StatementBlock) d.get(BasicSnippetData.Key.TARGET_BLOCK);
        final StatementBlock sb =
                new BlockContractRule.ValidityProgramConstructor(labels, block,
                                                                 variables,
                                                                 exceptionParameter,
                                                                 d.services).construct();
        final Statement s = new MethodFrame(null, context, sb);
        final JavaBlock result = JavaBlock.createJavaBlock(new StatementBlock(s));

        return result;
    }
}
