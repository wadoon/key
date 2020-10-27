package recoder.kit.pattern;

import recoder.ModelElement;

public interface DesignPattern extends ModelElement {
    int getParticipantCount();

    ModelElement getParticipantAt(int paramInt);
}
