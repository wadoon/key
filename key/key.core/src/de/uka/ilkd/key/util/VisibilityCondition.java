package de.uka.ilkd.key.util;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.MessageTypeValue;
import de.uka.ilkd.key.speclang.translation.SLExpression;

public class VisibilityCondition {
    private final SLExpression componentContext;
    private final IProgramMethod serviceContext; 
    private final MessageType messageType;
    private final Term term;
    private final Direction direction;
    
    public enum Direction {
        IN, OUT
    }
    
    public enum MessageType {
        CALL, TERMINATION
    }

    public VisibilityCondition(SLExpression componentContext,
            IProgramMethod serviceContext, MessageType messageType, Direction direction, Term term) {
        this.componentContext = componentContext;
        this.serviceContext = serviceContext;
        this.messageType = messageType;
        this.term = term;
        this.direction = direction;
    }

    public SLExpression getComponentContext() {
        return componentContext;
    }

    public IProgramMethod getServiceContext() {
        return serviceContext;
    }

    public MessageType getMessageType() {
        return messageType;
    }

    public Term getTerm() {
        return term;
    }

    @Override
    public String toString() {
        return "(" + direction.name() + ")" + componentContext.getTerm() + "." + serviceContext.getName() + "." + messageType.name() + "(" + term + ")";
    }

    public Direction getDirection() {
        return direction;
    }
    
}
