package de.uka.ilkd.key.util;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.MessageTypeValue;
import de.uka.ilkd.key.speclang.translation.SLExpression;

public class VisibilityCondition {
    private final SLExpression componentContext;
    private final IProgramMethod serviceContext; 
    private final MessageTypeValue messageType;
    private final Term term;

    public VisibilityCondition(SLExpression componentContext,
            IProgramMethod serviceContext, MessageTypeValue messageType, Term term) {
        this.componentContext = componentContext;
        this.serviceContext = serviceContext;
        this.messageType = messageType;
        this.term = term;
    }

    public SLExpression getComponentContext() {
        return componentContext;
    }

    public IProgramMethod getServiceContext() {
        return serviceContext;
    }

    public MessageTypeValue getMessageType() {
        return messageType;
    }

    public Term getTerm() {
        return term;
    }

    @Override
    public String toString() {
        return componentContext.getTerm() + "." + serviceContext.getName() + "." + messageType.name() + "(" + term + ")";
    }
    
}
