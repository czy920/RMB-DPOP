package edu.cqu.algorithms;

import edu.cqu.core.FinishedListener;
import edu.cqu.core.Solver;
import edu.cqu.result.Result;

public class Test {
    public static void main(String[] args){//NEW_MBDPOP6_k2,DPOP
        Solver solver = new Solver();
        solver.solve("am.xml", "rmbdpop",
                "problems/RANDOM_DCOP_24_3_density_0.2_0.xml", new FinishedListener() {
                    @Override
                    public void onFinished(Result result) {



                    }
                }, false, false);
    }
}
