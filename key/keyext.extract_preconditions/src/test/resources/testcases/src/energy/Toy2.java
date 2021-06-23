final class Sensor {

    /*@ normal_behavior
      @ ensures \result > 0;
      @ assignable \strictly_nothing;
      @*/
    int getWindSpeed();
}

final class Generator {

    final int maxWindSpeed;
    final Capacitor c;

    /*@ normal_behavior
      @ ensures this.c == c;
      @ ensures this.maxWindSpeed == maxWindSpeed;
      @ assignable \nothing;
      @*/
    Generator(Capacitor c, int maxWindSpeed) { this.c = c; this.maxWindSpeed = maxWindSpeed; }

    /*@ normal_behavior
      @ requires windSpeed <= maxWindSpeed;
      @ ensures c.charge == \old(c.charge + windSpeed);
      @ assignable c.charge;
      @*/
    void run(int windSpeed) {
        if (windSpeed > maxWindSpeed) {
             throw new RuntimeException();
        }
        
        c.charge += windSpeed;
    }
}

final class Capacitor {

    int charge;

    final int maxCharge;

    //@ instance invariant 0 <= charge && charge <= maxCharge;

    /*@ normal_behavior
      @ requires maxCharge >= 0;
      @ ensures this.maxCharge == maxCharge;
      @ assignable \nothing;
      @*/
    Capacitor(int maxCharge) { this.maxCharge = maxCharge; }
}

final class Monitor {

    final boolean checkState(int windSpeed, Generator g) {
        return windSpeed < g.maxWindSpeed && g.c.charge < g.c.maxCharge;
    }
}

final class Main {

    /*@ normal_behavior
      @ requires g.c == c;
      @ requires \invariant_for(c);
      @ ensures \invariant_for(c);
      @*/
    void main0(Sensor s, Capacitor c, Generator g, Monitor m) {
        int windSpeed = s.getWindSpeed();
        if (m.checkState(windSpeed, g)) {
            g.run(windSpeed);
        }
    }

    /*@ normal_behavior
      @ requires windSpeed > 0;
      @ requires g.c == c;
      @ requires \invariant_for(c);
      @ ensures \invariant_for(c);
      @*/
    void main1(Sensor s, Capacitor c, Generator g, Monitor m, int windSpeed) {
        if (m.checkState(windSpeed, g)) {
            g.run(windSpeed);
        }
    }
}

