import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.classLoader.*;
import com.ibm.wala.core.tests.callGraph.CallGraphTestUtil;
import com.ibm.wala.dataflow.graph.BitVectorSolver;
import com.ibm.wala.fixpoint.BitVectorVariable;
import com.ibm.wala.fixpoint.IFixedPointSystem;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.FakeRootClass;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.impl.DefaultEntrypoint;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.cfg.BasicBlockInContext;
import com.ibm.wala.ipa.cfg.ExplodedInterproceduralCFG;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ipa.cha.IClassHierarchy;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.SSACFG;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.analysis.IExplodedBasicBlock;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.graph.INodeWithNumber;
import com.ibm.wala.util.graph.impl.NodeWithNumber;
import org.javatuples.Pair;
import soot.PackManager;
import soot.Transform;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.jar.JarFile;


public class Main {
    static Set<String> classpath_set = new HashSet<>();
    static List<String> entry_claz_list = new ArrayList<>();


    static void addClassPathToScope(String classPath, AnalysisScope scope, ClassLoaderReference loader) {
        if (classPath == null) {
            throw new IllegalArgumentException("null classPath");
        } else {
            try {
                StringTokenizer paths = new StringTokenizer(classPath, File.pathSeparator);
                while(true) {
                    while(paths.hasMoreTokens()) {
                        String path = paths.nextToken();
                        if (classpath_set.contains(path)){
                            continue;
                        } else {
                            classpath_set.add(path);
                        }
                        if (path.endsWith(".jar")) {
                            JarFile jar = new JarFile(path, false);
                            scope.addToScope(loader, jar);
                        } else {
                            File f = new File(path);
                            if (f.isDirectory()) {
                                scope.addToScope(loader, new BinaryDirectoryTreeModule(f));
                            } else {
                                scope.addClassFileToScope(loader, f);
                            }
                        }
                    }
                    return;
                }
            } catch (InvalidClassFileException | IOException var12) {
            }
        }
    }

    static AnalysisScope constructScope(String classpath) throws IOException {
        AnalysisScope scope = AnalysisScopeReader.makePrimordialScope(null);
        ClassLoaderReference loader = scope.getLoader(AnalysisScope.APPLICATION);
        addClassPathToScope(classpath, scope, loader);
        return scope;
    }

    static void getDFG(String proj_path, String save_path) throws Exception{
        AnalysisScope scope = constructScope(proj_path);
        IClassHierarchy cha = ClassHierarchyFactory.make(scope);
        Iterable<Entrypoint> entrypoints = Util.makeMainEntrypoints(scope, cha);
        for (IClass klass : cha) {
            if(klass.getClassLoader().getName().toString().equals("Application")) {
                String name = klass.getName().toString();
                entry_claz_list.add(name.replace('/', '.').substring(1));
            }
        }
        AnalysisOptions options = CallGraphTestUtil.makeAnalysisOptions(scope, entrypoints);
        System.out.println("Call Graph Start");
        CallGraphBuilder<InstanceKey> builder = Util.makeZeroOneCFABuilder(Language.JAVA,
                options, new AnalysisCacheImpl(), cha, scope);
        CallGraph cg = builder.makeCallGraph(options, null);
        System.out.println("Call Graph Done");
        ExplodedInterproceduralCFG icfg = ExplodedInterproceduralCFG.make(cg);
        System.out.println("CFG block size " + icfg.getNumberOfNodes());
        Map<Integer, String> nodes = new HashMap<>();
        List<Pair<Integer, Integer>> edgelist = new ArrayList<>();
        for(BasicBlockInContext<IExplodedBasicBlock> basicblock: icfg){
            IMethod m = basicblock.getMethod();
            IClass klass = m.getDeclaringClass();
            if(klass.getClassLoader().getName().toString().equals("Application")){

                int instruction_index = basicblock.getFirstInstructionIndex();
                int line_no = -1;
                if(instruction_index >= 0) {
                    line_no = m.getLineNumber(instruction_index);
                }
                String src_name = klass.getName().toString().replace('/', '.').substring(1) + ".java";
                String blk_line = src_name + ":" + line_no;
                nodes.put(icfg.getNumber(basicblock), blk_line);
            }
        }
        ContextInsensitiveReachingDefs reachingDefs = new ContextInsensitiveReachingDefs(icfg, cha);
        System.out.println("DFG Start");
        BitVectorSolver<BasicBlockInContext<IExplodedBasicBlock>> solver = reachingDefs.analyze();
        IFixedPointSystem<BitVectorVariable> system = solver.getFixedPointSystem();
        for(BasicBlockInContext<IExplodedBasicBlock> basicblock: icfg){
            IMethod m = basicblock.getMethod();
            IClass klass = m.getDeclaringClass();
            if(klass.getClassLoader().getName().toString().equals("Application")){
                int u = icfg.getNumber(basicblock);
                BitVectorVariable var = solver.getOut(basicblock);
                Iterator<NodeWithNumber> succs = (Iterator<NodeWithNumber>) system.getStatementsThatUse(var);
                while(succs.hasNext()){
                    NodeWithNumber node = succs.next();
                    int v = node.getGraphNodeId();
                    edgelist.add(Pair.with(u, v));
                }
            }
        }
        File node_file = new File(save_path + ".nodelist");
        File edge_file = new File(save_path + ".edgelist");
        FileWriter writer = new FileWriter(node_file);
        Set<Map.Entry<Integer, String>> entries = nodes.entrySet();
        for(Map.Entry<Integer, String> entry : entries) {
            writer.write(entry.getKey() + " ;;;; " + entry.getValue() + "\n");
        }
        writer.close();
        writer = new FileWriter(edge_file);
        for(Pair<Integer, Integer> edge : edgelist){
            writer.write(edge.getValue0() + " " + edge.getValue1() + " 1\n");
            writer.write(edge.getValue1() + " " + edge.getValue0() + " -1\n");
        }
        writer.close();
    }


    public static void main(String[] args) {
        String proj_path = args[0];
        String dfg_output_path = args[1];
        String pdg_output_path = args[2];
        System.out.println(proj_path);
        try {
            getDFG(proj_path, dfg_output_path);
            System.out.println("WALA task done.");
            System.out.println("Start Soot task.");

            StringBuilder classpath = new StringBuilder(
                    System.getenv("JAVA_HOME") + File.separator + "lib" + File.separator + "tools.jar"
                            + File.pathSeparator + System.getenv("JAVA_HOME") + File.separator + "jre/lib" + File.separator + "rt.jar"
                            + File.pathSeparator + System.getenv("JAVA_HOME") + File.separator + "jre/lib" + File.separator + "jce.jar"
                            + File.pathSeparator + proj_path
            );
            Saver.setPath(pdg_output_path);
            List<String> Args = new ArrayList<>();
            PackManager.v().getPack("wjtp").add(new Transform("wjtp.trans", new PDGTransform()));
            Args.add("--keep-line-number");
            Args.add("-w");
            Args.add("-p");
            Args.add("wjtp.trans");
            Args.add("enabled:true");
            Args.add("-p");
            Args.add("cg.spark");
            Args.add("enabled:true");
            Args.add("-allow-phantom-refs");
            Args.add("--soot-class-path");
            Args.add(classpath.toString());
            Args.addAll(entry_claz_list);
            soot.Main.main(Args.toArray(new String[Args.size()]));
	    Saver.save();
        } catch (Exception e){
            e.printStackTrace();
        }
    }
}
