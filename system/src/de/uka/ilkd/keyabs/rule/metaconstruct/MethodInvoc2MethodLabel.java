package de.uka.ilkd.keyabs.rule.metaconstruct;

import java.util.Iterator;

import abs.frontend.ast.InterfaceDecl;
import abs.frontend.ast.MethodSig;
import abs.frontend.ast.ParamDecl;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.keyabs.abs.ABSProgramElement;
import de.uka.ilkd.keyabs.abs.ABSServices;
import de.uka.ilkd.keyabs.proof.init.FunctionBuilder;
import de.uka.ilkd.keyabs.logic.ABSTermBuilder;

public class MethodInvoc2MethodLabel extends AbstractTermTransformer {

    public MethodInvoc2MethodLabel() {
        super(new Name("#methodInvoc2MethodLabel"), 2);
    }

    @Override
    public Term transform(Term term, SVInstantiations svInst, IServices services) {

        ABSServices serv = (ABSServices) services;

        Term callee = term.sub(0);

        SchemaVariable argsSV = (SchemaVariable) term.sub(1).op();
        Iterable<ABSProgramElement> args = (Iterable<ABSProgramElement>) svInst.getInstantiation(argsSV);

        Debug.assertTrue(args instanceof Iterable);
        TermBuilder TB = services.getTermBuilder();
        Term seq = TB.seqEmpty(services);



        ProgramElement pe = (ProgramElement) svInst.lookupValue(new Name("m"));
        String methName = pe.toString();

        System.out.println("Looking for " + callee.sort().name());

        InterfaceDecl itf = serv.getJavaInfo().getABSParserInfo().getInterfaces().get(callee.sort().name());
        System.out.println("Returned itf name " + itf);
        Function mlabel = null;
        for (MethodSig msig : itf.getBodys()) {
            System.out.println(msig.getName() + " == " + methName);
            if (methName.equals(msig.getName())) {
                mlabel = (Function) serv.getNamespaces().functions().
                        lookup(FunctionBuilder.createNameFor(msig, itf));
                break;
            }
        }

        return ABSTermBuilder.TB.func(mlabel);
    }

    private boolean compatibleArgs(MethodSig msig, Iterable<ABSProgramElement> args,
                                   ABSServices services) {

        Iterator<ABSProgramElement> it = args.iterator();
        for (ParamDecl pd : msig.getParamList()) {
            if (it.hasNext()) {
                Sort s = services.getTypeConverter().convertToLogicElement(it.next()).sort();
                if (!s.extendsTrans(services.getJavaInfo().
                        getKeYJavaType(pd.getType().getQualifiedName()).getSort())) {
                    return false;
                }
            } else {
                return false;
            }

        }
        return !it.hasNext();
    }

}
