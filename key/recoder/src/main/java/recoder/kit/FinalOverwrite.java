package recoder.kit;

import recoder.abstraction.Member;

public class FinalOverwrite extends Conflict {
    private static final long serialVersionUID = -4261490216982913161L;

    private final Member member;

    public FinalOverwrite(Member member) {
        this.member = member;
    }

    public Member getMember() {
        return this.member;
    }
}
