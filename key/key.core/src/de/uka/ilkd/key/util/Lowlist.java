package de.uka.ilkd.key.util;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.translation.SLExpression;

public class Lowlist {
    
    private final SLExpression component;
    private final IProgramMethod service;
    private final ImmutableList<Term> lowTerms;
    private final Direction direction;
    private final MessageType callType;
    private final SLExpression partner;
    
    public enum Direction {
        IN, OUT
    }
    
    public enum MessageType {
        CALL, TERMINATION
    }

    public Lowlist(SLExpression component, IProgramMethod service, SLExpression partner, Direction direction, MessageType callType,
            ImmutableList<Term> lowTerms) {
        this.component = component;
        this.service = service;
        this.lowTerms = lowTerms;
        this.direction = direction;
        this.callType = callType;
        this.partner = partner;
    }

    public SLExpression getComponent() {
        return component;
    }

    public IProgramMethod getService() {
        return service;
    }

    public SLExpression getCommunicationPartner() {        
        return partner;
    }
    
    public ImmutableList<Term> getLowTerms() {
        return lowTerms;
    }
    
    public Direction getDirection() {
        return direction;
    }
    
    @Override
    public String toString() {
        return component.getTerm() + "." + service.getName() + "." + direction.name() + lowTerms;
    }

    public MessageType getCallType() {
        return callType;
    }
    

}
