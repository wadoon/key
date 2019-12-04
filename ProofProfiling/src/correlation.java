import org.apache.commons.math3.stat.correlation.PearsonsCorrelation;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.math3.stat.correlation.Covariance;

public class correlation {
	
	public void correlationStatitics(List<Double> depth, List<Long> time) throws Exception {
		double[] x = new double[depth.size()];
		for (int i = 0; i < x.length; i++) {
			x[i] = depth.get(i);                
		}
		
		double[] y = new double[time.size()];
		for (int i = 0; i < y.length; i++) {
			y[i] = time.get(i).doubleValue();            
		}
        
        System.out.println("x: " + Arrays.toString(x));
        System.out.println("y: " + Arrays.toString(y));
        System.out.println("Covariance: " + new Covariance().covariance(x,y));
        System.out.println("Pearson's Correlation: " + new PearsonsCorrelation().correlation(x,y));
      
    }

}
