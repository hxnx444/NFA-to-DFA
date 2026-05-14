package nfa_dfa_project;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Scanner;

class Node {
    int val;
    Node next;

    Node(int v) {
        val = v;
    }
}

class StateSet {
    Node head;
    int size = 0;

    void insert(int v) {
        if (!exists(v)) {
            Node n = new Node(v);
            n.next = head;
            head = n;
            size++;
        }
    }

    boolean exists(int v) {
        Node cur = head;
        while (cur != null) {
            if (cur.val == v) return true;
            cur = cur.next;
        }
        return false;
    }

    boolean isEqual(StateSet other) {
        if (this.size != other.size) return false;
        Node cur = this.head;
        while (cur != null) {
            if (!other.exists(cur.val)) return false;
            cur = cur.next;
        }
        return true;
    }
}

class CharStack {
    char[] data = new char[100];
    int top = -1;

    void push(char c) {
        data[++top] = c;
    }

    char pop() {
        return data[top--];
    }

    char peek() {
        return data[top];
    }

    boolean isEmpty() {
        return top != -1;
    }
}

class NFAFragment {
    int start, accept;

    NFAFragment(int s, int a) {
        start = s;
        accept = a;
    }
}

class FragStack {
    NFAFragment[] data = new NFAFragment[100];
    int top = -1;

    void push(NFAFragment f) {
        data[++top] = f;
    }

    NFAFragment pop() {
        return data[top--];
    }
}

class NFAState {
    int id;
    char[] chars = new char[10];
    int[][] targets = new int[10][10];
    int[] tCount = new int[10];
    int[] eps = new int[10];
    int epsCount = 0;

    NFAState(int i) {
        id = i;
    }

    void addTrans(char c, int next) {
        if (c == 'E') {
            eps[epsCount++] = next;
        } else {
            for (int i = 0; i < 10; i++) {
                if (chars[i] == c || chars[i] == '\0') {
                    chars[i] = c;
                    targets[i][tCount[i]++] = next;
                    break;
                }
            }
        }
    }
}

class NFA {
    NFAState[] q = new NFAState[500];
    int start, accept;
}

class DFAState {
    String name;
    StateSet nfaStates;
    boolean isFinal = false;
    char[] inputs = new char[10];
    DFAState[] next = new DFAState[10];
    int transCount = 0;

    DFAState(String n, StateSet s) {
        name = n;
        nfaStates = s;
    }

    void link(char c, DFAState dest) {
        inputs[transCount] = c;
        next[transCount] = dest;
        transCount++;
    }
}

class Edge {
    String from, to;
    char label;

    Edge(String f, String t, char l) {
        from = f;
        to = t;
        label = l;
    }
}

class RegexToNFA {
    int stateCounter = 0;
    NFAState[] states = new NFAState[500];

    int newState() {
        states[stateCounter] = new NFAState(stateCounter);
        return stateCounter++;
    }

    int precedence(char c) {
        if (c == '*' || c == '+' || c == '?') return 3;
        if (c == '.') return 2;
        if (c == '|') return 1;
        return 0;
    }

    String addConcat(String r) {
        String out = "";
        for (int i = 0; i < r.length(); i++) {
            char c1 = r.charAt(i);
            out += c1;
            if (i + 1 < r.length()) {
                char c2 = r.charAt(i + 1);
                boolean leftOk = c1 != '(' && c1 != '|' && c1 != '.';
                boolean rightOk = c2 != ')' && c2 != '*' && c2 != '|' && c2 != '?' && c2 != '+' && c2 != '.';
                if (leftOk && rightOk) out += '.';
            }
        }
        return out;
    }

    String toPostfix(String r) {
        String dotted = addConcat(r);
        String postfix = "";
        CharStack stack = new CharStack();

        for (int i = 0; i < dotted.length(); i++) {
            char c = dotted.charAt(i);
            if (Character.isLetterOrDigit(c)) {
                postfix += c;
            } else if (c == '(') {
                stack.push(c);
            } else if (c == ')') {
                while (stack.isEmpty() && stack.peek() != '(') postfix += stack.pop();
                stack.pop();
            } else {
                while (stack.isEmpty() && stack.peek() != '(' && precedence(stack.peek()) >= precedence(c))
                    postfix += stack.pop();
                stack.push(c);
            }
        }
        while (stack.isEmpty()) postfix += stack.pop();
        return postfix;
    }

    NFA buildNFA(String postfix) {
        FragStack stack = new FragStack();

        for (int i = 0; i < postfix.length(); i++) {
            char c = postfix.charAt(i);

            if (c == '*') {
                NFAFragment f = stack.pop();
                int s = newState(), a = newState();
                states[s].addTrans('E', f.start);
                states[s].addTrans('E', a);
                states[f.accept].addTrans('E', f.start);
                states[f.accept].addTrans('E', a);
                stack.push(new NFAFragment(s, a));

            } else if (c == '+') {
                NFAFragment f = stack.pop();
                int a = newState();
                states[f.accept].addTrans('E', f.start);
                states[f.accept].addTrans('E', a);
                stack.push(new NFAFragment(f.start, a));

            } else if (c == '?') {
                NFAFragment f = stack.pop();
                int s = newState(), a = newState();
                states[s].addTrans('E', f.start);
                states[s].addTrans('E', a);
                states[f.accept].addTrans('E', a);
                stack.push(new NFAFragment(s, a));

            } else if (c == '.') {
                NFAFragment f2 = stack.pop(), f1 = stack.pop();
                states[f1.accept].addTrans('E', f2.start);
                stack.push(new NFAFragment(f1.start, f2.accept));

            } else if (c == '|') {
                NFAFragment f2 = stack.pop(), f1 = stack.pop();
                int s = newState(), a = newState();
                states[s].addTrans('E', f1.start);
                states[s].addTrans('E', f2.start);
                states[f1.accept].addTrans('E', a);
                states[f2.accept].addTrans('E', a);
                stack.push(new NFAFragment(s, a));

            } else {
                int s = newState(), a = newState();
                states[s].addTrans(c, a);
                stack.push(new NFAFragment(s, a));
            }
        }

        NFAFragment done = stack.pop();
        NFA nfa = new NFA();
        nfa.q = states;
        nfa.start = done.start;
        nfa.accept = done.accept;
        return nfa;
    }
}

class Converter {

    StateSet epsClosure(StateSet init, NFA nfa) {
        StateSet res = new StateSet();
        int[] stack = new int[500];
        int top = -1;

        Node cur = init.head;
        while (cur != null) {
            res.insert(cur.val);
            stack[++top] = cur.val;
            cur = cur.next;
        }

        while (top >= 0) {
            int id = stack[top--];
            NFAState s = nfa.q[id];
            for (int i = 0; i < s.epsCount; i++) {
                int nx = s.eps[i];
                if (!res.exists(nx)) {
                    res.insert(nx);
                    stack[++top] = nx;
                }
            }
        }
        return res;
    }

    DFAState[] nfaToDfa(NFA nfa, char[] lang) {
        DFAState[] dfa = new DFAState[200];
        int count = 0;

        StateSet s0 = new StateSet();
        s0.insert(nfa.start);
        StateSet c0 = epsClosure(s0, nfa);

        DFAState start = new DFAState("Q0", c0);
        start.isFinal = c0.exists(nfa.accept);
        dfa[count++] = start;

        for (int i = 0; i < count; i++) {
            DFAState cur = dfa[i];

            for (char sym : lang) {
                StateSet moved = new StateSet();
                Node n = cur.nfaStates.head;

                while (n != null) {
                    NFAState ns = nfa.q[n.val];
                    for (int j = 0; j < 10; j++) {
                        if (ns.chars[j] == sym) {
                            for (int k = 0; k < ns.tCount[j]; k++)
                                moved.insert(ns.targets[j][k]);
                            break;
                        }
                    }
                    n = n.next;
                }

                StateSet closure = epsClosure(moved, nfa);
                if (closure.size == 0) continue;

                DFAState target = null;
                for (int k = 0; k < count; k++) {
                    if (dfa[k].nfaStates.isEqual(closure)) {
                        target = dfa[k];
                        break;
                    }
                }

                if (target == null) {
                    target = new DFAState("Q" + count, closure);
                    target.isFinal = closure.exists(nfa.accept);
                    dfa[count++] = target;
                }
                cur.link(sym, target);
            }
        }
        return Arrays.copyOf(dfa, count);
    }

    DFAState[] minimizeDFA(DFAState[] dfa, char[] lang) {
        int n = dfa.length;
        if (n == 0) return new DFAState[0];

        int[] part = new int[n];
        for (int i = 0; i < n; i++) part[i] = dfa[i].isFinal ? 1 : 0;

        boolean changed = true;
        while (changed) {
            changed = false;
            int[] nx = new int[n];
            int id = 0;

            for (int i = 0; i < n; i++) {
                if (nx[i] != 0) continue;
                nx[i] = ++id;
                for (int j = i + 1; j < n; j++) {
                    if (part[i] != part[j]) continue;
                    boolean same = true;
                    for (char ch : lang) {
                        DFAState ni = findNext(dfa[i], ch);
                        DFAState nj = findNext(dfa[j], ch);
                        int gi = (ni == null) ? -1 : part[indexOf(dfa, ni)];
                        int gj = (nj == null) ? -1 : part[indexOf(dfa, nj)];
                        if (gi != gj) {
                            same = false;
                            break;
                        }
                    }
                    if (same) nx[j] = id;
                }
            }

            for (int i = 0; i < n; i++) {
                if (part[i] != nx[i]) {
                    changed = true;
                    break;
                }
            }
            part = nx;
        }

        int numGroups = 0;
        for (int p : part) if (p > numGroups) numGroups = p;

        DFAState[] minDfa = new DFAState[numGroups];
        int startGroup = part[0];

        minDfa[0] = new DFAState("M0", new StateSet());
        int mIdx = 1;
        int[] groupToMinIdx = new int[numGroups + 1];
        groupToMinIdx[startGroup] = 0;

        for (int g = 1; g <= numGroups; g++) {
            if (g == startGroup) continue;
            minDfa[mIdx] = new DFAState("M" + mIdx, new StateSet());
            groupToMinIdx[g] = mIdx++;
        }

        boolean[] processed = new boolean[numGroups + 1];
        for (int i = 0; i < n; i++) {
            int g = part[i];
            if (processed[g]) continue;
            processed[g] = true;

            int newIdx = groupToMinIdx[g];
            minDfa[newIdx].isFinal = dfa[i].isFinal;

            for (char ch : lang) {
                DFAState nx = findNext(dfa[i], ch);
                if (nx != null) {
                    int nxGroup = part[indexOf(dfa, nx)];
                    minDfa[newIdx].link(ch, minDfa[groupToMinIdx[nxGroup]]);
                }
            }
        }
        return minDfa;
    }

    void printTable(DFAState[] dfa, char[] lang, String title) {
        System.out.println("\n" + title);
        System.out.println("-------------------------------------------------------");
        System.out.print("State\t");
        for (char ch : lang) System.out.print(ch + "\t");
        System.out.println("Final?");

        for (DFAState d : dfa) {
            System.out.print(d.name + "\t");
            for (char ch : lang) {
                DFAState nx = findNext(d, ch);
                System.out.print((nx == null ? "-" : nx.name) + "\t");
            }
            System.out.println(d.isFinal ? "Yes" : "No");
        }
        System.out.println("-------------------------------------------------------");
    }

    public void exportNFADot(NFA nfa, int totalStates, String filename) {
        try (OutputStreamWriter writer = new OutputStreamWriter(new FileOutputStream(filename), StandardCharsets.UTF_8)) {
            writer.write("digraph NFA {\n    rankdir=LR;\n    node [shape=circle];\n");
            writer.write("    \"" + nfa.accept + "\" [shape=doublecircle];\n");
            writer.write("    \"\" [shape=none];\n    \"\" -> \"" + nfa.start + "\";\n");

            for (int i = 0; i < totalStates; i++) {
                NFAState s = nfa.q[i];
                if (s == null) continue;
                for (int j = 0; j < s.epsCount; j++)
                    writer.write("    \"" + s.id + "\" -> \"" + s.eps[j] + "\" [label=\"ε\"];\n");
                for (int c = 0; c < 10; c++) {
                    if (s.chars[c] == '\0') break;
                    for (int k = 0; k < s.tCount[c]; k++)
                        writer.write("    \"" + s.id + "\" -> \"" + s.targets[c][k] + "\" [label=\"" + s.chars[c] + "\"];\n");
                }
            }
            writer.write("}\n");
        } catch (IOException ignored) {
        }
    }

    public void exportDFADot(DFAState[] dfa, char[] alphabet, String filename, Edge[] pathHighlights, int pathLen) {
        try (OutputStreamWriter writer = new OutputStreamWriter(new FileOutputStream(filename), StandardCharsets.UTF_8)) {
            writer.write("digraph DFA {\n    rankdir=LR;\n    node [shape=circle];\n");
            for (DFAState s : dfa) if (s.isFinal) writer.write("    \"" + s.name + "\" [shape=doublecircle];\n");
            writer.write("    \"\" [shape=none];\n    \"\" -> \"" + dfa[0].name + "\";\n");

            for (DFAState s : dfa) {
                for (char c : alphabet) {
                    DFAState dest = findNext(s, c);
                    if (dest != null) {
                        boolean highlight = false;
                        if (pathHighlights != null) {
                            for (int i = 0; i < pathLen; i++) {
                                Edge e = pathHighlights[i];
                                if (e.from.equals(s.name) && e.to.equals(dest.name) && e.label == c) {
                                    highlight = true;
                                    break;
                                }
                            }
                        }
                        String styling = highlight ? " [label=\"" + c + "\", color=\"red\", fontcolor=\"red\", penwidth=2.0]" : " [label=\"" + c + "\"]";
                        writer.write("    \"" + s.name + "\" -> \"" + dest.name + "\"" + styling + ";\n");
                    }
                }
            }
            writer.write("}\n");
        } catch (IOException ignored) {
        }
    }

    public void renderImageAutomatically(String gvFilename, String pngFilename) {
        try {
            String dotPath = "C:\\Program Files\\Graphviz\\bin\\dot.exe";
            ProcessBuilder pb = new ProcessBuilder(dotPath, "-Tpng", gvFilename, "-o", pngFilename);
            Process p = pb.start();
            p.waitFor();
            System.out.println("📸 Image auto-generated: " + pngFilename);
        } catch (Exception e) {
            System.out.println("⚠️ Could not auto-generate " + pngFilename + " (Check Graphviz path).");
        }
    }

    DFAState findNext(DFAState s, char c) {
        for (int i = 0; i < s.transCount; i++)
            if (s.inputs[i] == c) return s.next[i];
        return null;
    }

    int indexOf(DFAState[] arr, DFAState s) {
        for (int i = 0; i < arr.length; i++)
            if (arr[i] == s) return i;
        return -1;
    }
}

public class main {

    static void main(String[] args) {
        Scanner sc = new Scanner(System.in);

        System.out.println("         Bonus project  REGEX -> NFA -> DFA -> MIN                  ");
        System.out.println("=======================================================================");

        while (true) {
            System.out.print("\nEnter regex (type 'exit' to quit): ");
            String regex = sc.nextLine().replace(" ", "");

            if (regex.equalsIgnoreCase("exit")) break;

            if (!validate(regex)) {
                System.out.println("[ERROR] Bad regex -- check parentheses and operators.");
                continue;
            }

            RegexToNFA builder = new RegexToNFA();
            String postfix = builder.toPostfix(regex);
            NFA nfa = builder.buildNFA(postfix);
            char[] alpha = extractAlpha(regex);
            Converter conv = new Converter();

            DFAState[] dfa = conv.nfaToDfa(nfa, alpha);

            DFAState[] minDfa = conv.minimizeDFA(dfa, alpha);

            System.out.println("\n[Generating Graphviz Diagrams...]");
            conv.exportNFADot(nfa, builder.stateCounter, "nfa.gv");
            conv.renderImageAutomatically("nfa.gv", "nfa.png");

            conv.exportDFADot(dfa, alpha, "dfa.gv", null, 0);
            conv.renderImageAutomatically("dfa.gv", "dfa.png");

            conv.exportDFADot(minDfa, alpha, "min_dfa.gv", null, 0);
            conv.renderImageAutomatically("min_dfa.gv", "min_dfa.png");

            conv.printTable(dfa, alpha, "[STEP 2] NFA -> DFA TRANSITION TABLE");
            conv.printTable(minDfa, alpha, "[STEP 3] MINIMIZED DFA TRANSITION TABLE");

            System.out.println("\n[STEP 4] TEST STRINGS  (type 'back' for new regex, 'exit' to quit)");
            while (true) {
                System.out.print("  Input: ");
                String word = sc.nextLine();
                if (word.equalsIgnoreCase("back")) break;
                if (word.equalsIgnoreCase("exit")) {
                    sc.close();
                    return;
                }

                DFAState cur = minDfa[0];
                boolean rejected = false;
                Edge[] path = new Edge[100];
                int pCount = 0;

                for (int i = 0; i < word.length(); i++) {
                    char ch = word.charAt(i);
                    DFAState nx = conv.findNext(cur, ch);
                    if (nx == null) {
                        rejected = true;
                        break;
                    }
                    path[pCount++] = new Edge(cur.name, nx.name, ch);
                    cur = nx;
                }

                boolean accepted = !rejected && cur.isFinal;
                System.out.println("  Status: " + (accepted ? "✅ ACCEPTED" : "❌ REJECTED") + "\n");

                conv.exportDFADot(minDfa, alpha, "sim.gv", path, pCount);
                conv.renderImageAutomatically("sim.gv", "sim.png");
            }
        }
        sc.close();
    }

    static boolean validate(String r) {
        int depth = 0;
        for (int i = 0; i < r.length(); i++) {
            char c = r.charAt(i);
            if (c == '(') depth++;
            else if (c == ')') {
                if (--depth < 0) return false;
            } else if ((c == '*' || c == '+' || c == '?') && i == 0) return false;
            else if (c == '|' && (i == 0 || i == r.length() - 1)) return false;
        }
        return depth == 0;
    }

    static char[] extractAlpha(String r) {
        String ops = "()*|+?.";
        char[] buf = new char[128];
        int count = 0;
        for (int i = 0; i < r.length(); i++) {
            char c = r.charAt(i);
            if (Character.isLetterOrDigit(c) && !ops.contains(String.valueOf(c))) {
                boolean found = false;
                for (int j = 0; j < count; j++)
                    if (buf[j] == c) {
                        found = true;
                        break;
                    }
                if (!found) buf[count++] = c;
            }
        }
        return Arrays.copyOf(buf, count);
    }
}