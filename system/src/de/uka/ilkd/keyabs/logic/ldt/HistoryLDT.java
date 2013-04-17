package de.uka.ilkd.keyabs.logic.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.IServices;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.ldt.LDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.keyabs.abs.ABSServices;

public class HistoryLDT extends LDT {

    private final Sort interfaceLabelSort;
    private final Sort classLabelSort;
    private final Sort methodLabelSort;
    private final Sort futureSort;
    private LocationVariable history;
    private Function wellFormed;
    private Function invocationReactionEvent;

    public HistoryLDT(IServices services) {
        super(new Name("Seq"), services);

        interfaceLabelSort = services.getNamespaces().sorts()
                .lookup(new Name("ItfLabel"));
        classLabelSort = services.getNamespaces().sorts()
                .lookup(new Name("ClassLabel"));
        methodLabelSort = services.getNamespaces().sorts()
                .lookup(new Name("MethodLabel"));
        futureSort = services.getNamespaces().sorts()
                .lookup(new Name("Future"));

        history                 = (LocationVariable) services.getNamespaces().programVariables().lookup("history");
        wellFormed              = addFunction((Function) services.getNamespaces().functions().lookup("wfHist"));
        invocationReactionEvent = addFunction((Function) services.getNamespaces().functions().lookup("invocREv"));

    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, IServices services,
                                 ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right,
                                 IServices services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, IServices services,
                                 ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, IServices services) {
        return null;
    }

    @Override
    public Function getFunctionFor(Operator op, IServices services,
                                   ExecutionContext ec) {
        return null;
    }

    @Override
    public boolean hasLiteralFunction(Function f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, IServices services) {
        return null;
    }

    @Override
    public Type getType(Term t) {
        return null;
    }

    public Sort getInterfaceLabelSort() {
        return interfaceLabelSort;
    }

    public Sort getClassLabelSort() {
        return classLabelSort;
    }

    public Sort getMethodLabelSort() {
        return methodLabelSort;
    }

    public Sort getFutureSort() {
        return futureSort;
    }

    public Function getClassLabel(Name className, ABSServices services) {
        return (Function) services.getNamespaces().functions().lookup(className);
    }

    public LocationVariable getHistory() {
        return history;
    }

    public Function getWellFormed() {
        return wellFormed;
    }

    public Function getInvocationReactionEvent() {
        return invocationReactionEvent;
    }
}
