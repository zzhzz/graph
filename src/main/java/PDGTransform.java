import org.javatuples.Pair;
import soot.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.graph.pdg.*;
import soot.util.Chain;
import soot.util.queue.QueueReader;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.lang.Math;

public class PDGTransform extends SceneTransformer {
    List<ProgramDependenceGraph> graphs = new ArrayList<>();
    Map<PDGNode, Integer> indexOfnode = new HashMap<PDGNode, Integer>();
    @Override
    protected void internalTransform(String s, Map<String, String> map) {
        Chain<SootClass> classes = Scene.v().getClasses();
        for(SootClass sootClass : classes){
            String path = sootClass.getFilePath();
            if(sootClass.isApplicationClass()){
                List<SootMethod> ms = sootClass.getMethods();
                for(SootMethod m : ms){
                    if(m.hasActiveBody()){
                        UnitGraph g = new BriefUnitGraph(m.retrieveActiveBody());
                        try{
                            ProgramDependenceGraph pdg = new HashMutablePDG(g);
                            graphs.add(pdg);
                        } catch (Exception e){
                            continue;
                        }
                    }
                }
            }
        }
        int idx = 0;
        List<String> nodes = new ArrayList<>();
        List<Pair<Integer, Integer>> edges = new ArrayList<>();
        for(ProgramDependenceGraph g : graphs){
            for(PDGNode node : g){
                indexOfnode.put(node, idx);
                int lineno = -1;
                Object tmp = node.getNode();
                if(tmp instanceof Block) {
                    lineno = ((Block) tmp).getTail().getJavaSourceStartLineNumber();
                } else if(tmp instanceof PDGRegion || tmp instanceof Region){
                    List<Block> list = ((IRegion) tmp).getBlocks();
                    for(Block blk : list){
                        Unit u = blk.getTail();
                        lineno = Math.max(lineno, u.getJavaSourceStartLineNumber());
                    }
                } else {
                    System.out.println(tmp.getClass());
                    System.exit(1);
                }
                String path = g.getBlockGraph().getBody().getMethod().getDeclaringClass().getFilePath();
                String lineinfo = path + ":" + lineno;
                nodes.add(lineinfo);
                idx++;
            }
        }
        for(ProgramDependenceGraph g : graphs){
            for(PDGNode node : g){
                int u = indexOfnode.get(node);
                List<PDGNode> succs = g.getSuccsOf(node);
                for(PDGNode succNode : succs){
                    int v = indexOfnode.get(succNode);
                    edges.add(Pair.with(u, v));
                }
            }
        }
        Saver.addGraph(nodes, edges);
    }
}
