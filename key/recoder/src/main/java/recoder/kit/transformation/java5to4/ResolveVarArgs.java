package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Method;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.operator.NewArray;
import recoder.java.reference.MemberReference;
import recoder.java.reference.MethodReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.TypeKit;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

public class ResolveVarArgs extends TwoPassTransformation {
    private final CompilationUnit cu;

    private List<MethodDeclaration> varArgMeths;

    private List<MethodReference> refs;

    private List<List<Type>> sigs;

    private List<Type> lastParamTypes;

    public ResolveVarArgs(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    public ProblemReport analyze() {
        this.varArgMeths = new ArrayList<MethodDeclaration>();
        this.refs = new ArrayList<MethodReference>();
        this.sigs = new ArrayList<List<Type>>();
        this.lastParamTypes = new ArrayList<Type>();
        TreeWalker tw = new TreeWalker(this.cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) pe;
                if (md.isVarArgMethod()) {
                    this.varArgMeths.add(md);
                    this.lastParamTypes.add(getSourceInfo().getType(md.getParameterDeclarationAt(md.getParameterDeclarationCount() - 1).getTypeReference()));
                    List<MemberReference> rl = getCrossReferenceSourceInfo().getReferences(md);
                    for (int i = 0, s = rl.size(); i < s; i++) {
                        MethodReference toAdd = (MethodReference) rl.get(i);
                        if (toAdd.getArguments() != null && toAdd.getArguments().size() == md.getParameterDeclarationCount()) {
                            int idx = toAdd.getArguments().size() - 1;
                            Type tt = getSourceInfo().getType(toAdd.getExpressionAt(idx));
                            if (tt instanceof recoder.abstraction.ArrayType && tt.equals(getSourceInfo().getType(md.getParameterDeclarationAt(idx).getVariableSpecification())))
                                continue;
                        }
                        this.refs.add(toAdd);
                        this.sigs.add(getSourceInfo().getMethod(toAdd).getSignature());
                        continue;
                    }
                }
            }
        }
        return setProblemReport(NO_PROBLEM);
    }

    public void transform() {
        super.transform();
        ProgramFactory f = getProgramFactory();
        int idx = 0;
        for (MethodReference mr : this.refs) {
            List<Type> sig = this.sigs.get(idx++);
            int from = sig.size() - 1;
            int cnt = (mr.getArguments() == null) ? 0 : (mr.getArguments().size() - from);
            ASTArrayList aSTArrayList = new ASTArrayList(cnt);
            for (int i = 0; i < cnt; i++)
                aSTArrayList.add(mr.getArguments().get(from + i).deepClone());
            ArrayInitializer ai = f.createArrayInitializer(aSTArrayList);
            NewArray na = f.createNewArray(TypeKit.createTypeReference(f, sig.get(sig.size() - 1)), 0, ai);
            MethodReference repl = mr.deepClone();
            while (cnt-- > 0)
                repl.getArguments().remove(repl.getArguments().size() - 1);
            if (repl.getArguments() == null)
                repl.setArguments(new ASTArrayList(0));
            repl.getArguments().add(na);
            repl.makeParentRoleValid();
            replace(mr, repl);
        }
        idx = 0;
        for (MethodDeclaration md : this.varArgMeths) {
            MethodDeclaration repl = md.deepClone();
            ASTList<ParameterDeclaration> aSTList = md.getParameters();
            ParameterDeclaration pd = aSTList.get(aSTList.size() - 1);
            ParameterDeclaration newpd = f.createParameterDeclaration(TypeKit.createTypeReference(f, getNameInfo().createArrayType(this.lastParamTypes.get(idx++))), pd.getVariableSpecification().getIdentifier().deepClone());
            newpd.setVarArg(false);
            replace(repl.getParameterDeclarationAt(repl.getParameterDeclarationCount() - 1), newpd);
            repl.makeParentRoleValid();
            replace(md, repl);
        }
    }
}
