"use client";
import React, { useState, useEffect, useRef, useCallback } from 'react';
import { motion, AnimatePresence } from 'framer-motion';
import * as d3 from 'd3';
import { Play, Pause, SkipForward, RotateCcw, Copy, Check, Zap, Turtle, Grid3x3, Sparkles, Info, ChevronDown, ChevronUp } from 'lucide-react';
import confetti from 'canvas-confetti';

// ==================== REGEX TO DFA ALGORITHMS ====================

class NFAState {
  constructor(id) {
    this.id = id;
    this.transitions = {}; // { symbol: [states] }
    this.epsilonTransitions = [];
    this.isAccept = false;
  }
}

class DFAState {
  constructor(id, nfaStates = []) {
    this.id = id;
    this.nfaStates = nfaStates;
    this.transitions = {}; // { symbol: state }
    this.isAccept = false;
  }
}

// Parse regex and build NFA
function regexToNFA(regex) {
  let stateCounter = 0;
  
  function newState() {
    return new NFAState(stateCounter++);
  }
  
  function parseAtom(pos) {
    if (pos >= regex.length) return null;
    
    const char = regex[pos];
    if (char === '(') {
      return parseUnion(pos + 1);
    } else if (char !== '+' && char !== '*' && char !== ')') {
      const start = newState();
      const end = newState();
      start.transitions[char] = [end];
      return { start, end, nextPos: pos + 1 };
    }
    return null;
  }
  
  function parseStar(pos) {
    const atom = parseAtom(pos);
    if (!atom) return null;
    
    let { start, end, nextPos } = atom;
    
    if (nextPos < regex.length && regex[nextPos] === '*') {
      const newStart = newState();
      const newEnd = newState();
      
      newStart.epsilonTransitions.push(start);
      newStart.epsilonTransitions.push(newEnd);
      end.epsilonTransitions.push(start);
      end.epsilonTransitions.push(newEnd);
      
      return { start: newStart, end: newEnd, nextPos: nextPos + 1 };
    }
    
    return { start, end, nextPos };
  }
  
  function parseConcat(pos) {
    const first = parseStar(pos);
    if (!first) return null;
    
    let current = first;
    
    while (current.nextPos < regex.length) {
      const char = regex[current.nextPos];
      if (char === ')' || char === '+') break;
      
      const next = parseStar(current.nextPos);
      if (!next) break;
      
      current.end.epsilonTransitions.push(next.start);
      current = { start: current.start, end: next.end, nextPos: next.nextPos };
    }
    
    return current;
  }
  
  function parseUnion(pos) {
    const left = parseConcat(pos);
    if (!left) return null;
    
    let nextPos = left.nextPos;
    
    if (nextPos < regex.length && regex[nextPos] === '+') {
      const right = parseUnion(nextPos + 1);
      if (!right) return left;
      
      const start = newState();
      const end = newState();
      
      start.epsilonTransitions.push(left.start);
      start.epsilonTransitions.push(right.start);
      left.end.epsilonTransitions.push(end);
      right.end.epsilonTransitions.push(end);
      
      nextPos = right.nextPos;
      
      if (nextPos < regex.length && regex[nextPos] === ')') {
        nextPos++;
      }
      
      return { start, end, nextPos };
    }
    
    if (nextPos < regex.length && regex[nextPos] === ')') {
      return { ...left, nextPos: nextPos + 1 };
    }
    
    return left;
  }
  
  const result = parseUnion(0);
  if (!result) return null;
  
  result.end.isAccept = true;
  return result;
}

// Epsilon closure
function epsilonClosure(states) {
  const closure = new Set(states);
  const stack = [...states];
  
  while (stack.length > 0) {
    const state = stack.pop();
    for (const nextState of state.epsilonTransitions) {
      if (!closure.has(nextState)) {
        closure.add(nextState);
        stack.push(nextState);
      }
    }
  }
  
  return Array.from(closure);
}

// NFA to DFA conversion
function nfaToDFA(nfa, alphabet) {
  if (!nfa) return null;
  
  const dfaStates = [];
  const dfaStateMap = new Map();
  let dfaStateCounter = 0;
  
  function getStateId(nfaStates) {
    const key = nfaStates.map(s => s.id).sort().join(',');
    if (dfaStateMap.has(key)) {
      return dfaStateMap.get(key);
    }
    const newState = new DFAState(`q${dfaStateCounter++}`, nfaStates);
    newState.isAccept = nfaStates.some(s => s.isAccept);
    dfaStates.push(newState);
    dfaStateMap.set(key, newState);
    return newState;
  }
  
  const startClosure = epsilonClosure([nfa.start]);
  const startState = getStateId(startClosure);
  
  const unmarked = [startState];
  const marked = new Set();
  
  while (unmarked.length > 0) {
    const currentDFAState = unmarked.pop();
    if (marked.has(currentDFAState)) continue;
    marked.add(currentDFAState);
    
    for (const symbol of alphabet) {
      const reachable = [];
      for (const nfaState of currentDFAState.nfaStates) {
        if (nfaState.transitions[symbol]) {
          reachable.push(...nfaState.transitions[symbol]);
        }
      }
      
      if (reachable.length > 0) {
        const closure = epsilonClosure(reachable);
        const nextDFAState = getStateId(closure);
        currentDFAState.transitions[symbol] = nextDFAState;
        
        if (!marked.has(nextDFAState)) {
          unmarked.push(nextDFAState);
        }
      }
    }
  }
  
  return { states: dfaStates, start: startState, alphabet };
}

// Minimize DFA
function minimizeDFA(dfa) {
  if (!dfa || !dfa.states || dfa.states.length === 0) return dfa;
  
  const states = dfa.states;
  const alphabet = dfa.alphabet;
  
  // Partition into accept and non-accept states
  let partitions = [
    states.filter(s => s.isAccept),
    states.filter(s => !s.isAccept)
  ].filter(p => p.length > 0);
  
  let changed = true;
  while (changed) {
    changed = false;
    const newPartitions = [];
    
    for (const partition of partitions) {
      if (partition.length === 1) {
        newPartitions.push(partition);
        continue;
      }
      
      const groups = new Map();
      
      for (const state of partition) {
        const signature = alphabet.map(symbol => {
          const nextState = state.transitions[symbol];
          if (!nextState) return -1;
          return partitions.findIndex(p => p.includes(nextState));
        }).join(',');
        
        if (!groups.has(signature)) {
          groups.set(signature, []);
        }
        groups.get(signature).push(state);
      }
      
      const groupArrays = Array.from(groups.values());
      if (groupArrays.length > 1) {
        changed = true;
      }
      newPartitions.push(...groupArrays);
    }
    
    partitions = newPartitions;
  }
  
  // Build minimized DFA
  const minimizedStates = partitions.map((partition, idx) => {
    const newState = new DFAState(`q${idx}`);
    newState.isAccept = partition[0].isAccept;
    return { newState, oldStates: partition };
  });
  
  const stateMap = new Map();
  minimizedStates.forEach(({ newState, oldStates }) => {
    oldStates.forEach(oldState => {
      stateMap.set(oldState, newState);
    });
  });
  
  minimizedStates.forEach(({ newState, oldStates }) => {
    const representative = oldStates[0];
    for (const symbol of alphabet) {
      if (representative.transitions[symbol]) {
        newState.transitions[symbol] = stateMap.get(representative.transitions[symbol]);
      }
    }
  });
  
  const minimizedStart = stateMap.get(dfa.start);
  
  return {
    states: minimizedStates.map(m => m.newState),
    start: minimizedStart,
    alphabet
  };
}

// Get alphabet from regex
function getAlphabet(regex) {
  const chars = new Set();
  for (const char of regex) {
    if (char !== '+' && char !== '*' && char !== '(' && char !== ')') {
      chars.add(char);
    }
  }
  return Array.from(chars).sort();
}

// Build DFA from regex
function buildDFA(regex) {
  try {
    const alphabet = getAlphabet(regex);
    const nfa = regexToNFA(regex);
    if (!nfa) return null;
    
    const dfa = nfaToDFA(nfa, alphabet);
    if (!dfa) return null;
    
    return minimizeDFA(dfa);
  } catch (e) {
    console.error('Error building DFA:', e);
    return null;
  }
}

// Simulate string on DFA
function simulateDFA(dfa, input) {
  if (!dfa || !dfa.start) return { accepted: false, path: [] };
  
  let currentState = dfa.start;
  const path = [currentState];
  
  for (const char of input) {
    if (!currentState.transitions[char]) {
      return { accepted: false, path, failedAt: char };
    }
    currentState = currentState.transitions[char];
    path.push(currentState);
  }
  
  return { accepted: currentState.isAccept, path };
}

// Generate strings from DFA
function generateStrings(dfa, count, minLen, maxLen, charSet) {
  if (!dfa || !dfa.start) return [];
  
  const strings = new Set();
  const queue = [{ state: dfa.start, str: '' }];
  
  while (queue.length > 0 && strings.size < count) {
    const { state, str } = queue.shift();
    
    if (str.length >= minLen && str.length <= maxLen && state.isAccept) {
      strings.add(str);
    }
    
    if (str.length < maxLen) {
      for (const char of charSet) {
        if (state.transitions[char]) {
          queue.push({ state: state.transitions[char], str: str + char });
        }
      }
    }
  }
  
  return Array.from(strings).slice(0, count);
}

// Check equivalence
function checkEquivalence(dfa1, dfa2) {
  if (!dfa1 || !dfa2) return { equivalent: false };
  
  // Simple structural comparison
  if (dfa1.states.length !== dfa2.states.length) {
    return { equivalent: false, reason: 'Different number of states' };
  }
  
  // Find a counterexample by exploring strings
  const alphabet = [...new Set([...dfa1.alphabet, ...dfa2.alphabet])];
  const maxLen = 10;
  
  for (let len = 0; len <= maxLen; len++) {
    const strings = generateAllStrings(alphabet, len);
    for (const str of strings) {
      const result1 = simulateDFA(dfa1, str);
      const result2 = simulateDFA(dfa2, str);
      
      if (result1.accepted !== result2.accepted) {
        return {
          equivalent: false,
          counterexample: str,
          dfa1Accepts: result1.accepted,
          dfa2Accepts: result2.accepted
        };
      }
    }
  }
  
  return { equivalent: true };
}

function generateAllStrings(alphabet, length) {
  if (length === 0) return [''];
  const strings = [];
  const shorter = generateAllStrings(alphabet, length - 1);
  for (const str of shorter) {
    for (const char of alphabet) {
      strings.push(str + char);
    }
  }
  return strings;
}

// ==================== COMPONENTS ====================

// DFA Graph Visualization Component
function DFAGraph({ dfa, activeState, activeTransition, onStateClick, height = 400 }) {
  const svgRef = useRef();
  const [positions, setPositions] = useState({});
  const [dragging, setDragging] = useState(null);
  const [transform, setTransform] = useState({ x: 0, y: 0, scale: 1 });
  
  useEffect(() => {
    if (!dfa || !dfa.states) return;
    
    // Initial layout in a circle
    const radius = 120;
    const centerX = 250;
    const centerY = height / 2;
    
    const newPositions = {};
    dfa.states.forEach((state, i) => {
      const angle = (i / dfa.states.length) * 2 * Math.PI;
      newPositions[state.id] = {
        x: centerX + radius * Math.cos(angle),
        y: centerY + radius * Math.sin(angle)
      };
    });
    
    setPositions(newPositions);
  }, [dfa, height]);
  
  useEffect(() => {
    if (!dfa || !svgRef.current || Object.keys(positions).length === 0) return;
    
    const svg = d3.select(svgRef.current);
    svg.selectAll('*').remove();
    
    const g = svg.append('g')
      .attr('transform', `translate(${transform.x}, ${transform.y}) scale(${transform.scale})`);
    
    // Draw transitions
    const transitions = [];
    dfa.states.forEach(state => {
      Object.entries(state.transitions).forEach(([symbol, nextState]) => {
        transitions.push({ from: state, to: nextState, symbol });
      });
    });
    
    transitions.forEach(trans => {
      const fromPos = positions[trans.from.id];
      const toPos = positions[trans.to.id];
      
      if (!fromPos || !toPos) return;
      
      const isActive = activeTransition &&
        activeTransition.from === trans.from.id &&
        activeTransition.to === trans.to.id;
      
      // Self-loop
      if (trans.from === trans.to) {
        const loopSize = 30;
        g.append('path')
          .attr('d', `M ${fromPos.x} ${fromPos.y - 25}
                      Q ${fromPos.x + loopSize} ${fromPos.y - loopSize - 25}
                        ${fromPos.x} ${fromPos.y - 25}`)
          .attr('fill', 'none')
          .attr('stroke', isActive ? '#06b6d4' : '#6b7280')
          .attr('stroke-width', isActive ? 3 : 2)
          .attr('marker-end', 'url(#arrowhead)')
          .style('filter', isActive ? 'drop-shadow(0 0 8px #06b6d4)' : 'none');
        
        g.append('text')
          .attr('x', fromPos.x + loopSize / 2)
          .attr('y', fromPos.y - loopSize - 30)
          .attr('text-anchor', 'middle')
          .attr('fill', '#e5e7eb')
          .attr('font-size', '14px')
          .attr('font-family', 'JetBrains Mono, monospace')
          .text(trans.symbol);
      } else {
        // Curved line
        const dx = toPos.x - fromPos.x;
        const dy = toPos.y - fromPos.y;
        const dist = Math.sqrt(dx * dx + dy * dy);
        const curve = 30;
        
        const midX = (fromPos.x + toPos.x) / 2;
        const midY = (fromPos.y + toPos.y) / 2;
        const perpX = -dy / dist * curve;
        const perpY = dx / dist * curve;
        
        const path = g.append('path')
          .attr('d', `M ${fromPos.x} ${fromPos.y}
                      Q ${midX + perpX} ${midY + perpY}
                        ${toPos.x} ${toPos.y}`)
          .attr('fill', 'none')
          .attr('stroke', isActive ? '#06b6d4' : '#6b7280')
          .attr('stroke-width', isActive ? 3 : 2)
          .attr('marker-end', 'url(#arrowhead)')
          .style('filter', isActive ? 'drop-shadow(0 0 8px #06b6d4)' : 'none');
        
        // Particle animation on active transition
        if (isActive) {
          const pathNode = path.node();
          const length = pathNode.getTotalLength();
          
          for (let i = 0; i < 3; i++) {
            const circle = g.append('circle')
              .attr('r', 3)
              .attr('fill', '#06b6d4')
              .style('filter', 'drop-shadow(0 0 4px #06b6d4)');
            
            const animate = () => {
              const duration = 1000;
              const offset = (i / 3) * duration;
              
              circle
                .attr('opacity', 0)
                .transition()
                .delay(offset)
                .duration(0)
                .attr('opacity', 1)
                .transition()
                .duration(duration)
                .ease(d3.easeLinear)
                .attrTween('transform', () => {
                  return (t) => {
                    const point = pathNode.getPointAtLength(t * length);
                    return `translate(${point.x}, ${point.y})`;
                  };
                })
                .on('end', animate);
            };
            
            animate();
          }
        }
        
        g.append('text')
          .attr('x', midX + perpX)
          .attr('y', midY + perpY)
          .attr('text-anchor', 'middle')
          .attr('fill', '#e5e7eb')
          .attr('font-size', '14px')
          .attr('font-family', 'JetBrains Mono, monospace')
          .text(trans.symbol);
      }
    });
    
    // Draw states
    dfa.states.forEach(state => {
      const pos = positions[state.id];
      if (!pos) return;
      
      const isActive = activeState === state.id;
      const isStart = state === dfa.start;
      
      const stateGroup = g.append('g')
        .attr('transform', `translate(${pos.x}, ${pos.y})`)
        .style('cursor', 'pointer');
      
      // Glow effect for active state
      if (isActive) {
        stateGroup.append('circle')
          .attr('r', 35)
          .attr('fill', '#fbbf24')
          .attr('opacity', 0.3)
          .transition()
          .duration(500)
          .attr('r', 40)
          .attr('opacity', 0)
          .on('end', function repeat() {
            d3.select(this)
              .attr('r', 35)
              .attr('opacity', 0.3)
              .transition()
              .duration(500)
              .attr('r', 40)
              .attr('opacity', 0)
              .on('end', repeat);
          });
      }
      
      // Main circle
      stateGroup.append('circle')
        .attr('r', 25)
        .attr('fill', isActive ? '#fbbf24' : state.isAccept ? '#10b981' : '#374151')
        .attr('stroke', isStart ? '#3b82f6' : '#6b7280')
        .attr('stroke-width', isStart ? 3 : 2)
        .style('filter', state.isAccept ? 'drop-shadow(0 0 6px #10b981)' : 'none');
      
      // Double circle for accept states
      if (state.isAccept) {
        stateGroup.append('circle')
          .attr('r', 20)
          .attr('fill', 'none')
          .attr('stroke', '#10b981')
          .attr('stroke-width', 2);
      }
      
      // State label
      stateGroup.append('text')
        .attr('text-anchor', 'middle')
        .attr('dy', 5)
        .attr('fill', '#f3f4f6')
        .attr('font-size', '14px')
        .attr('font-weight', 'bold')
        .text(state.id);
      
      // Start arrow
      if (isStart) {
        g.append('path')
          .attr('d', `M ${pos.x - 50} ${pos.y} L ${pos.x - 30} ${pos.y}`)
          .attr('stroke', '#3b82f6')
          .attr('stroke-width', 3)
          .attr('marker-end', 'url(#arrowhead-blue)');
      }
    });
    
    // Define arrowheads
    const defs = svg.append('defs');
    
    defs.append('marker')
      .attr('id', 'arrowhead')
      .attr('markerWidth', 10)
      .attr('markerHeight', 10)
      .attr('refX', 8)
      .attr('refY', 3)
      .attr('orient', 'auto')
      .append('polygon')
      .attr('points', '0 0, 10 3, 0 6')
      .attr('fill', '#6b7280');
    
    defs.append('marker')
      .attr('id', 'arrowhead-blue')
      .attr('markerWidth', 10)
      .attr('markerHeight', 10)
      .attr('refX', 8)
      .attr('refY', 3)
      .attr('orient', 'auto')
      .append('polygon')
      .attr('points', '0 0, 10 3, 0 6')
      .attr('fill', '#3b82f6');
    
  }, [dfa, positions, activeState, activeTransition, transform]);
  
  // Handle drag
  const handleMouseDown = (e) => {
    const rect = svgRef.current.getBoundingClientRect();
    const x = (e.clientX - rect.left - transform.x) / transform.scale;
    const y = (e.clientY - rect.top - transform.y) / transform.scale;
    
    // Find clicked state
    const clickedState = dfa?.states.find(state => {
      const pos = positions[state.id];
      if (!pos) return false;
      const dist = Math.sqrt((x - pos.x) ** 2 + (y - pos.y) ** 2);
      return dist < 25;
    });
    
    if (clickedState) {
      setDragging({ state: clickedState.id, offsetX: x - positions[clickedState.id].x, offsetY: y - positions[clickedState.id].y });
    }
  };
  
  const handleMouseMove = (e) => {
    if (!dragging) return;
    
    const rect = svgRef.current.getBoundingClientRect();
    const x = (e.clientX - rect.left - transform.x) / transform.scale;
    const y = (e.clientY - rect.top - transform.y) / transform.scale;
    
    setPositions(prev => ({
      ...prev,
      [dragging.state]: {
        x: x - dragging.offsetX,
        y: y - dragging.offsetY
      }
    }));
  };
  
  const handleMouseUp = () => {
    setDragging(null);
  };
  
  const handleWheel = (e) => {
    e.preventDefault();
    const delta = e.deltaY > 0 ? 0.9 : 1.1;
    setTransform(prev => ({
      ...prev,
      scale: Math.max(0.5, Math.min(3, prev.scale * delta))
    }));
  };
  
  const autoLayout = () => {
    if (!dfa) return;
    
    const radius = 120;
    const centerX = 250;
    const centerY = height / 2;
    
    const newPositions = {};
    dfa.states.forEach((state, i) => {
      const angle = (i / dfa.states.length) * 2 * Math.PI - Math.PI / 2;
      newPositions[state.id] = {
        x: centerX + radius * Math.cos(angle),
        y: centerY + radius * Math.sin(angle)
      };
    });
    
    setPositions(newPositions);
  };
  
  const resetView = () => {
    setTransform({ x: 0, y: 0, scale: 1 });
  };
  
  return (
    <div className="relative">
      <svg
        ref={svgRef}
        width="100%"
        height={height}
        onMouseDown={handleMouseDown}
        onMouseMove={handleMouseMove}
        onMouseUp={handleMouseUp}
        onMouseLeave={handleMouseUp}
        onWheel={handleWheel}
        className="bg-gray-900/30 rounded-lg border border-gray-700"
      />
      <div className="absolute bottom-4 right-4 flex gap-2">
        <button
          onClick={autoLayout}
          className="px-3 py-2 bg-purple-600 hover:bg-purple-500 text-white rounded-lg flex items-center gap-2 transition-all hover:scale-105 shadow-lg"
        >
          <Grid3x3 size={16} />
          Auto-Layout
        </button>
        <button
          onClick={resetView}
          className="px-3 py-2 bg-blue-600 hover:bg-blue-500 text-white rounded-lg flex items-center gap-2 transition-all hover:scale-105 shadow-lg"
        >
          <RotateCcw size={16} />
          Reset View
        </button>
      </div>
    </div>
  );
}

// Main App Component
export default function RegexVisualizer() {
  const [activeTab, setActiveTab] = useState('generator');
  const [showGuide, setShowGuide] = useState(false);
  
  return (
    <div className="min-h-screen bg-gradient-to-br from-gray-900 via-purple-900 to-gray-900 text-white p-8">
      <div className="max-w-7xl mx-auto">
        {/* Header */}
        <motion.div
          initial={{ opacity: 0, y: -20 }}
          animate={{ opacity: 1, y: 0 }}
          className="text-center mb-8"
        >
          <h1 className="text-5xl font-bold mb-4 bg-gradient-to-r from-purple-400 via-pink-400 to-blue-400 bg-clip-text text-transparent">
            Regular Expression Visualizer
          </h1>
          <p className="text-gray-300 text-lg">
            Visualize DFAs, Generate Strings, and Check Equivalence
          </p>
        </motion.div>
        
        {/* Guide Toggle */}
        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 1 }}
          transition={{ delay: 0.2 }}
          className="mb-6"
        >
          <button
            onClick={() => setShowGuide(!showGuide)}
            className="w-full px-6 py-4 bg-gradient-to-r from-blue-600/20 to-purple-600/20 border border-blue-500/30 rounded-xl flex items-center justify-between hover:border-blue-400/50 transition-all"
          >
            <div className="flex items-center gap-3">
              <Info size={24} className="text-blue-400" />
              <span className="text-lg font-semibold">How to Use This App</span>
            </div>
            {showGuide ? <ChevronUp size={24} /> : <ChevronDown size={24} />}
          </button>
          
          <AnimatePresence>
            {showGuide && (
              <motion.div
                initial={{ height: 0, opacity: 0 }}
                animate={{ height: 'auto', opacity: 1 }}
                exit={{ height: 0, opacity: 0 }}
                className="overflow-hidden"
              >
                <div className="mt-4 p-6 bg-gray-800/50 border border-gray-700 rounded-xl backdrop-blur">
                  <h3 className="text-xl font-bold mb-4 text-purple-400">Regex Notation</h3>
                  <div className="grid grid-cols-2 gap-4 mb-6">
                    <div className="p-4 bg-gray-900/50 rounded-lg">
                      <code className="text-green-400">+</code> → Union (a+b means "a OR b")
                    </div>
                    <div className="p-4 bg-gray-900/50 rounded-lg">
                      <code className="text-green-400">*</code> → Kleene Star (a* means "zero or more a's")
                    </div>
                    <div className="p-4 bg-gray-900/50 rounded-lg">
                      <code className="text-green-400">ab</code> → Concatenation (a then b)
                    </div>
                    <div className="p-4 bg-gray-900/50 rounded-lg">
                      <code className="text-green-400">( )</code> → Grouping
                    </div>
                  </div>
                  
                  <h3 className="text-xl font-bold mb-4 text-purple-400">Example Patterns</h3>
                  <div className="space-y-2">
                    <div className="p-3 bg-gray-900/50 rounded-lg flex justify-between items-center">
                      <code className="text-yellow-400">(a+b)*</code>
                      <span className="text-gray-400">Zero or more of (a or b)</span>
                    </div>
                    <div className="p-3 bg-gray-900/50 rounded-lg flex justify-between items-center">
                      <code className="text-yellow-400">a*b*</code>
                      <span className="text-gray-400">Zero or more a's, then zero or more b's</span>
                    </div>
                    <div className="p-3 bg-gray-900/50 rounded-lg flex justify-between items-center">
                      <code className="text-yellow-400">(a+b)*abb</code>
                      <span className="text-gray-400">Any a's and b's, ending with "abb"</span>
                    </div>
                  </div>
                </div>
              </motion.div>
            )}
          </AnimatePresence>
        </motion.div>
        
        {/* Tab Navigation */}
        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 1 }}
          transition={{ delay: 0.3 }}
          className="flex gap-4 mb-8"
        >
          <button
            onClick={() => setActiveTab('generator')}
            className={`flex-1 px-8 py-4 rounded-xl font-semibold text-lg transition-all ${
              activeTab === 'generator'
                ? 'bg-gradient-to-r from-purple-600 to-blue-600 shadow-lg shadow-purple-500/50 scale-105'
                : 'bg-gray-800/50 hover:bg-gray-700/50 border border-gray-700'
            }`}
          >
            🎲 String Generator
          </button>
          <button
            onClick={() => setActiveTab('equivalence')}
            className={`flex-1 px-8 py-4 rounded-xl font-semibold text-lg transition-all ${
              activeTab === 'equivalence'
                ? 'bg-gradient-to-r from-purple-600 to-blue-600 shadow-lg shadow-purple-500/50 scale-105'
                : 'bg-gray-800/50 hover:bg-gray-700/50 border border-gray-700'
            }`}
          >
            ⚖️ Equivalence Checker
          </button>
        </motion.div>
        
        {/* Tab Content */}
        <AnimatePresence mode="wait">
          {activeTab === 'generator' ? (
            <StringGeneratorTab key="generator" />
          ) : (
            <EquivalenceCheckerTab key="equivalence" />
          )}
        </AnimatePresence>
      </div>
    </div>
  );
}

// String Generator Tab
function StringGeneratorTab() {
  const [regex, setRegex] = useState('(a+b)*');
  const [dfa, setDfa] = useState(null);
  const [error, setError] = useState('');
  const [charSets, setCharSets] = useState({ az: true, AZ: false, num: false });
  const [numStrings, setNumStrings] = useState(20);
  const [minLen, setMinLen] = useState(0);
  const [maxLen, setMaxLen] = useState(5);
  const [generatedStrings, setGeneratedStrings] = useState([]);
  const [generating, setGenerating] = useState(false);
  const [testString, setTestString] = useState('');
  const [simulationState, setSimulationState] = useState(null);
  const [isSimulating, setIsSimulating] = useState(false);
  const [simulationSpeed, setSimulationSpeed] = useState(500);
  const [copiedIndex, setCopiedIndex] = useState(null);
  
  useEffect(() => {
    try {
      const built = buildDFA(regex);
      setDfa(built);
      setError('');
    } catch (e) {
      setError('Invalid regex syntax');
      setDfa(null);
    }
  }, [regex]);
  
  const insertSymbol = (symbol) => {
    setRegex(prev => prev + symbol);
  };
  
  const getCharSet = () => {
    let chars = '';
    if (charSets.az) chars += 'abcdefghijklmnopqrstuvwxyz';
    if (charSets.AZ) chars += 'ABCDEFGHIJKLMNOPQRSTUVWXYZ';
    if (charSets.num) chars += '0123456789';
    return chars.split('');
  };
  
  const handleGenerate = () => {
    if (!dfa) return;
    
    setGenerating(true);
    setTimeout(() => {
      const charSet = getCharSet();
      const strings = generateStrings(dfa, numStrings, minLen, maxLen, charSet);
      setGeneratedStrings(strings);
      setGenerating(false);
    }, 500);
  };
  
  const handleVerify = async () => {
    if (!dfa || !testString) return;
    
    setIsSimulating(true);
    const chars = testString.split('');
    let currentState = dfa.start;
    const path = [currentState];
    
    for (let i = 0; i < chars.length; i++) {
      const char = chars[i];
      
      setSimulationState({
        currentChar: char,
        currentCharIndex: i,
        currentState: currentState.id,
        path: path.map(s => s.id),
        processing: true
      });
      
      await new Promise(resolve => setTimeout(resolve, simulationSpeed));
      
      if (!currentState.transitions[char]) {
        setSimulationState({
          accepted: false,
          failedAt: char,
          path: path.map(s => s.id),
          processing: false
        });
        setIsSimulating(false);
        return;
      }
      
      currentState = currentState.transitions[char];
      path.push(currentState);
    }
    
    setSimulationState({
      accepted: currentState.isAccept,
      path: path.map(s => s.id),
      finalState: currentState.id,
      processing: false
    });
    
    if (currentState.isAccept) {
      confetti({
        particleCount: 100,
        spread: 70,
        origin: { y: 0.6 }
      });
    }
    
    setIsSimulating(false);
  };
  
  const copyString = (str, index) => {
    navigator.clipboard.writeText(str);
    setCopiedIndex(index);
    setTimeout(() => setCopiedIndex(null), 2000);
  };
  
  return (
    <motion.div
      initial={{ opacity: 0, x: -20 }}
      animate={{ opacity: 1, x: 0 }}
      exit={{ opacity: 0, x: 20 }}
      className="space-y-6"
    >
      {/* Regex Input Panel */}
      <div className="p-6 bg-gradient-to-br from-gray-800/50 to-gray-900/50 backdrop-blur border border-gray-700 rounded-xl shadow-2xl">
        <h2 className="text-2xl font-bold mb-4 text-purple-400">Regular Expression Input</h2>
        
        <input
          type="text"
          value={regex}
          onChange={(e) => setRegex(e.target.value)}
          className="w-full px-4 py-3 bg-gray-900/50 border border-gray-600 rounded-lg text-white font-mono text-lg focus:border-purple-500 focus:ring-2 focus:ring-purple-500/50 transition-all"
          placeholder="Enter regex (e.g., (a+b)*)"
        />
        
        <div className="mt-4">
          <p className="text-sm text-gray-400 mb-2">Symbol Palette:</p>
          <div className="flex flex-wrap gap-2">
            {['a', 'b', 'c', '+', '*', '(', ')'].map(symbol => (
              <button
                key={symbol}
                onClick={() => insertSymbol(symbol)}
                className="px-4 py-2 bg-gray-700 hover:bg-gray-600 rounded-lg font-mono transition-all hover:scale-105"
              >
                {symbol}
              </button>
            ))}
          </div>
        </div>
        
        <div className="mt-4">
          {error ? (
            <div className="flex items-center gap-2 text-red-400">
              <span className="text-xl">✗</span>
              <span>{error}</span>
            </div>
          ) : (
            <div className="flex items-center gap-2 text-green-400">
              <span className="text-xl">✓</span>
              <span>Valid syntax</span>
            </div>
          )}
        </div>
      </div>
      
      {/* String Generation Panel */}
      <div className="p-6 bg-gradient-to-br from-gray-800/50 to-gray-900/50 backdrop-blur border border-gray-700 rounded-xl shadow-2xl">
        <h2 className="text-2xl font-bold mb-4 text-blue-400">String Generation Settings</h2>
        
        <div className="grid grid-cols-3 gap-4 mb-4">
          <label className="flex items-center gap-2 cursor-pointer">
            <input
              type="checkbox"
              checked={charSets.az}
              onChange={(e) => setCharSets(prev => ({ ...prev, az: e.target.checked }))}
              className="w-5 h-5"
            />
            <span>a-z</span>
          </label>
          <label className="flex items-center gap-2 cursor-pointer">
            <input
              type="checkbox"
              checked={charSets.AZ}
              onChange={(e) => setCharSets(prev => ({ ...prev, AZ: e.target.checked }))}
              className="w-5 h-5"
            />
            <span>A-Z</span>
          </label>
          <label className="flex items-center gap-2 cursor-pointer">
            <input
              type="checkbox"
              checked={charSets.num}
              onChange={(e) => setCharSets(prev => ({ ...prev, num: e.target.checked }))}
              className="w-5 h-5"
            />
            <span>0-9</span>
          </label>
        </div>
        
        <div className="grid grid-cols-3 gap-4 mb-4">
          <div>
            <label className="block text-sm text-gray-400 mb-2">Number of Strings</label>
            <input
              type="number"
              value={numStrings}
              onChange={(e) => setNumStrings(parseInt(e.target.value) || 0)}
              className="w-full px-4 py-2 bg-gray-900/50 border border-gray-600 rounded-lg text-white"
              min="1"
              max="100"
            />
          </div>
          <div>
            <label className="block text-sm text-gray-400 mb-2">Min Length</label>
            <input
              type="number"
              value={minLen}
              onChange={(e) => setMinLen(parseInt(e.target.value) || 0)}
              className="w-full px-4 py-2 bg-gray-900/50 border border-gray-600 rounded-lg text-white"
              min="0"
            />
          </div>
          <div>
            <label className="block text-sm text-gray-400 mb-2">Max Length</label>
            <input
              type="number"
              value={maxLen}
              onChange={(e) => setMaxLen(parseInt(e.target.value) || 0)}
              className="w-full px-4 py-2 bg-gray-900/50 border border-gray-600 rounded-lg text-white"
              min={minLen}
            />
          </div>
        </div>
        
        <button
          onClick={handleGenerate}
          disabled={!dfa || generating}
          className="w-full px-6 py-4 bg-gradient-to-r from-purple-600 to-blue-600 hover:from-purple-500 hover:to-blue-500 disabled:from-gray-600 disabled:to-gray-700 rounded-xl font-bold text-lg shadow-lg hover:shadow-purple-500/50 transition-all hover:scale-105 disabled:scale-100"
        >
          {generating ? (
            <span className="flex items-center justify-center gap-2">
              <div className="w-5 h-5 border-2 border-white border-t-transparent rounded-full animate-spin" />
              Generating...
            </span>
          ) : (
            'Generate Strings'
          )}
        </button>
        
        {generatedStrings.length > 0 && (
          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            className="mt-6"
          >
            <h3 className="text-xl font-bold mb-4">
              Generated Strings ({generatedStrings.length} of {numStrings} requested)
            </h3>
            <div className="grid grid-cols-4 gap-4">
              {generatedStrings.map((str, index) => (
                <motion.div
                  key={index}
                  initial={{ opacity: 0, y: 20 }}
                  animate={{ opacity: 1, y: 0 }}
                  transition={{ delay: index * 0.05 }}
                  className="p-4 bg-gradient-to-br from-gray-700/50 to-gray-800/50 rounded-lg border border-gray-600 hover:border-purple-500 hover:scale-105 transition-all group"
                >
                  <div className="font-mono text-lg mb-2 break-all">{str || '(empty)'}</div>
                  <div className="text-sm text-gray-400 mb-2">Length: {str.length}</div>
                  <button
                    onClick={() => copyString(str, index)}
                    className="w-full px-3 py-1 bg-purple-600/20 hover:bg-purple-600/40 rounded flex items-center justify-center gap-2 transition-all"
                  >
                    {copiedIndex === index ? (
                      <>
                        <Check size={14} />
                        Copied!
                      </>
                    ) : (
                      <>
                        <Copy size={14} />
                        Copy
                      </>
                    )}
                  </button>
                </motion.div>
              ))}
            </div>
          </motion.div>
        )}
      </div>
      
      {/* String Verification Panel */}
      <div className="p-6 bg-gradient-to-br from-gray-800/50 to-gray-900/50 backdrop-blur border border-gray-700 rounded-xl shadow-2xl">
        <h2 className="text-2xl font-bold mb-4 text-green-400">String Verification & DFA Simulation</h2>
        
        <div className="flex gap-4 mb-4">
          <input
            type="text"
            value={testString}
            onChange={(e) => setTestString(e.target.value)}
            className="flex-1 px-4 py-3 bg-gray-900/50 border border-gray-600 rounded-lg text-white font-mono text-lg"
            placeholder="Enter test string"
          />
          <button
            onClick={handleVerify}
            disabled={!dfa || !testString || isSimulating}
            className="px-8 py-3 bg-gradient-to-r from-green-600 to-blue-600 hover:from-green-500 hover:to-blue-500 disabled:from-gray-600 disabled:to-gray-700 rounded-lg font-bold shadow-lg transition-all hover:scale-105"
          >
            Verify
          </button>
        </div>
        
        <div className="mb-4">
          <label className="block text-sm text-gray-400 mb-2">Simulation Speed</label>
          <div className="flex items-center gap-4">
            <Turtle size={20} />
            <input
              type="range"
              min="100"
              max="2000"
              step="100"
              value={simulationSpeed}
              onChange={(e) => setSimulationSpeed(parseInt(e.target.value))}
              className="flex-1"
            />
            <Zap size={20} />
          </div>
        </div>
        
        {dfa && (
          <DFAGraph
            dfa={dfa}
            activeState={simulationState?.currentState}
            activeTransition={
              simulationState?.processing && simulationState.path.length > 1
                ? {
                    from: simulationState.path[simulationState.path.length - 2],
                    to: simulationState.currentState
                  }
                : null
            }
            height={400}
          />
        )}
        
        {simulationState && !simulationState.processing && (
          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            className={`mt-6 p-6 rounded-xl border-2 ${
              simulationState.accepted
                ? 'bg-green-900/20 border-green-500'
                : 'bg-red-900/20 border-red-500'
            }`}
          >
            <div className="text-2xl font-bold mb-2">
              {simulationState.accepted ? '✅ ACCEPTED' : '❌ REJECTED'}
            </div>
            <div className="text-gray-300">
              Path: {simulationState.path.join(' → ')}
            </div>
            {simulationState.failedAt && (
              <div className="text-red-400 mt-2">
                Failed at character: "{simulationState.failedAt}"
              </div>
            )}
          </motion.div>
        )}
      </div>
    </motion.div>
  );
}

// Equivalence Checker Tab
function EquivalenceCheckerTab() {
  const [regex1, setRegex1] = useState('(a+b)*');
  const [regex2, setRegex2] = useState('(b+a)*');
  const [dfa1, setDfa1] = useState(null);
  const [dfa2, setDfa2] = useState(null);
  const [error1, setError1] = useState('');
  const [error2, setError2] = useState('');
  const [checking, setChecking] = useState(false);
  const [result, setResult] = useState(null);
  const [testString, setTestString] = useState('');
  const [simulation, setSimulation] = useState(null);
  const [simulationSpeed, setSimulationSpeed] = useState(500);
  const [isSimulating, setIsSimulating] = useState(false);
  
  useEffect(() => {
    try {
      const built = buildDFA(regex1);
      setDfa1(built);
      setError1('');
    } catch (e) {
      setError1('Invalid syntax');
      setDfa1(null);
    }
  }, [regex1]);
  
  useEffect(() => {
    try {
      const built = buildDFA(regex2);
      setDfa2(built);
      setError2('');
    } catch (e) {
      setError2('Invalid syntax');
      setDfa2(null);
    }
  }, [regex2]);
  
  const handleCheck = () => {
    if (!dfa1 || !dfa2) return;
    
    setChecking(true);
    setTimeout(() => {
      const equivalence = checkEquivalence(dfa1, dfa2);
      setResult(equivalence);
      setChecking(false);
      
      if (equivalence.equivalent) {
        confetti({
          particleCount: 150,
          spread: 100,
          origin: { y: 0.5 }
        });
      }
    }, 1500);
  };
  
  const handleSimulate = async () => {
    if (!dfa1 || !dfa2 || !testString) return;
    
    setIsSimulating(true);
    const chars = testString.split('');
    
    let state1 = dfa1.start;
    let state2 = dfa2.start;
    const path1 = [state1];
    const path2 = [state2];
    
    for (let i = 0; i < chars.length; i++) {
      const char = chars[i];
      
      setSimulation({
        currentChar: char,
        currentCharIndex: i,
        state1: state1.id,
        state2: state2.id,
        path1: path1.map(s => s.id),
        path2: path2.map(s => s.id),
        processing: true
      });
      
      await new Promise(resolve => setTimeout(resolve, simulationSpeed));
      
      if (state1.transitions[char]) {
        state1 = state1.transitions[char];
        path1.push(state1);
      }
      
      if (state2.transitions[char]) {
        state2 = state2.transitions[char];
        path2.push(state2);
      }
    }
    
    setSimulation({
      accepted1: state1.isAccept,
      accepted2: state2.isAccept,
      path1: path1.map(s => s.id),
      path2: path2.map(s => s.id),
      finalState1: state1.id,
      finalState2: state2.id,
      processing: false
    });
    
    if (state1.isAccept && state2.isAccept) {
      confetti({
        particleCount: 100,
        spread: 70,
        origin: { y: 0.6 }
      });
    }
    
    setIsSimulating(false);
  };
  
  return (
    <motion.div
      initial={{ opacity: 0, x: 20 }}
      animate={{ opacity: 1, x: 0 }}
      exit={{ opacity: 0, x: -20 }}
      className="space-y-6"
    >
      {/* Dual Input Panel */}
      <div className="grid grid-cols-2 gap-6">
        <div className="p-6 bg-gradient-to-br from-blue-900/20 to-gray-900/50 backdrop-blur border border-blue-700/30 rounded-xl shadow-2xl">
          <h2 className="text-2xl font-bold mb-4 text-blue-400">Regex 1</h2>
          <input
            type="text"
            value={regex1}
            onChange={(e) => setRegex1(e.target.value)}
            className="w-full px-4 py-3 bg-gray-900/50 border border-gray-600 rounded-lg text-white font-mono text-lg"
            placeholder="Enter regex 1"
          />
          <div className="mt-4 flex flex-wrap gap-2">
            {['a', 'b', 'c', '+', '*', '(', ')'].map(symbol => (
              <button
                key={symbol}
                onClick={() => setRegex1(prev => prev + symbol)}
                className="px-4 py-2 bg-gray-700 hover:bg-gray-600 rounded-lg font-mono transition-all hover:scale-105"
              >
                {symbol}
              </button>
            ))}
          </div>
          <div className="mt-4">
            {error1 ? (
              <div className="text-red-400">✗ {error1}</div>
            ) : (
              <div className="text-green-400">✓ Valid</div>
            )}
          </div>
        </div>
        
        <div className="p-6 bg-gradient-to-br from-purple-900/20 to-gray-900/50 backdrop-blur border border-purple-700/30 rounded-xl shadow-2xl">
          <h2 className="text-2xl font-bold mb-4 text-purple-400">Regex 2</h2>
          <input
            type="text"
            value={regex2}
            onChange={(e) => setRegex2(e.target.value)}
            className="w-full px-4 py-3 bg-gray-900/50 border border-gray-600 rounded-lg text-white font-mono text-lg"
            placeholder="Enter regex 2"
          />
          <div className="mt-4 flex flex-wrap gap-2">
            {['a', 'b', 'c', '+', '*', '(', ')'].map(symbol => (
              <button
                key={symbol}
                onClick={() => setRegex2(prev => prev + symbol)}
                className="px-4 py-2 bg-gray-700 hover:bg-gray-600 rounded-lg font-mono transition-all hover:scale-105"
              >
                {symbol}
              </button>
            ))}
          </div>
          <div className="mt-4">
            {error2 ? (
              <div className="text-red-400">✗ {error2}</div>
            ) : (
              <div className="text-green-400">✓ Valid</div>
            )}
          </div>
        </div>
      </div>
      
      {/* Check Button */}
      <button
        onClick={handleCheck}
        disabled={!dfa1 || !dfa2 || checking}
        className="w-full px-6 py-4 bg-gradient-to-r from-purple-600 to-blue-600 hover:from-purple-500 hover:to-blue-500 disabled:from-gray-600 disabled:to-gray-700 rounded-xl font-bold text-lg shadow-lg hover:shadow-purple-500/50 transition-all hover:scale-105"
      >
        {checking ? (
          <span className="flex items-center justify-center gap-2">
            <div className="w-5 h-5 border-2 border-white border-t-transparent rounded-full animate-spin" />
            Checking Equivalence...
          </span>
        ) : (
          'Check Equivalence'
        )}
      </button>
      
      {/* Result Banner */}
      <AnimatePresence>
        {result && (
          <motion.div
            initial={{ opacity: 0, y: -20 }}
            animate={{ opacity: 1, y: 0 }}
            exit={{ opacity: 0, y: -20 }}
            className={`p-6 rounded-xl border-2 ${
              result.equivalent
                ? 'bg-green-900/20 border-green-500'
                : 'bg-red-900/20 border-red-500'
            }`}
          >
            <div className="text-3xl font-bold mb-4">
              {result.equivalent ? '✅ EQUIVALENT' : '❌ NOT EQUIVALENT'}
            </div>
            
            {result.equivalent ? (
              <div>
                <p className="text-lg mb-4">These regular expressions are structurally identical!</p>
                <p className="text-gray-300">Both DFAs accept the same language.</p>
              </div>
            ) : (
              <div>
                <p className="text-lg mb-4">These regular expressions differ!</p>
                {result.counterexample && (
                  <div className="p-4 bg-gray-900/50 rounded-lg">
                    <p className="font-bold mb-2">Counterexample found: "{result.counterexample}"</p>
                    <div className="grid grid-cols-2 gap-4 mt-4">
                      <div className={result.dfa1Accepts ? 'text-green-400' : 'text-red-400'}>
                        DFA 1: {result.dfa1Accepts ? '✅ ACCEPTS' : '❌ REJECTS'}
                      </div>
                      <div className={result.dfa2Accepts ? 'text-green-400' : 'text-red-400'}>
                        DFA 2: {result.dfa2Accepts ? '✅ ACCEPTS' : '❌ REJECTS'}
                      </div>
                    </div>
                    <button
                      onClick={() => setTestString(result.counterexample)}
                      className="mt-4 px-4 py-2 bg-purple-600 hover:bg-purple-500 rounded-lg transition-all"
                    >
                      Test Counterexample
                    </button>
                  </div>
                )}
              </div>
            )}
          </motion.div>
        )}
      </AnimatePresence>
      
      {/* Dual DFA Visualization */}
      <div className="grid grid-cols-2 gap-6">
        <div className="p-6 bg-gradient-to-br from-blue-900/20 to-gray-900/50 backdrop-blur border border-blue-700/30 rounded-xl">
          <h2 className="text-xl font-bold mb-4 text-blue-400">Minimized DFA 1</h2>
          {dfa1 && (
            <>
              <DFAGraph
                dfa={dfa1}
                activeState={simulation?.state1}
                activeTransition={
                  simulation?.processing && simulation.path1.length > 1
                    ? {
                        from: simulation.path1[simulation.path1.length - 2],
                        to: simulation.state1
                      }
                    : null
                }
                height={400}
              />
              <div className="mt-4">
                <h3 className="font-bold mb-2">Transition Table</h3>
                <div className="overflow-auto max-h-60">
                  <table className="w-full text-sm">
                    <thead>
                      <tr className="bg-gray-800">
                        <th className="p-2 border border-gray-700">State</th>
                        <th className="p-2 border border-gray-700">Input</th>
                        <th className="p-2 border border-gray-700">Next</th>
                      </tr>
                    </thead>
                    <tbody>
                      {dfa1.states.map(state =>
                        Object.entries(state.transitions).map(([symbol, next], idx) => (
                          <tr key={`${state.id}-${idx}`} className="hover:bg-gray-800/50">
                            <td className="p-2 border border-gray-700 font-mono">{state.id}</td>
                            <td className="p-2 border border-gray-700 font-mono">{symbol}</td>
                            <td className="p-2 border border-gray-700 font-mono">{next.id}</td>
                          </tr>
                        ))
                      )}
                    </tbody>
                  </table>
                </div>
              </div>
            </>
          )}
        </div>
        
        <div className="p-6 bg-gradient-to-br from-purple-900/20 to-gray-900/50 backdrop-blur border border-purple-700/30 rounded-xl">
          <h2 className="text-xl font-bold mb-4 text-purple-400">Minimized DFA 2</h2>
          {dfa2 && (
            <>
              <DFAGraph
                dfa={dfa2}
                activeState={simulation?.state2}
                activeTransition={
                  simulation?.processing && simulation.path2.length > 1
                    ? {
                        from: simulation.path2[simulation.path2.length - 2],
                        to: simulation.state2
                      }
                    : null
                }
                height={400}
              />
              <div className="mt-4">
                <h3 className="font-bold mb-2">Transition Table</h3>
                <div className="overflow-auto max-h-60">
                  <table className="w-full text-sm">
                    <thead>
                      <tr className="bg-gray-800">
                        <th className="p-2 border border-gray-700">State</th>
                        <th className="p-2 border border-gray-700">Input</th>
                        <th className="p-2 border border-gray-700">Next</th>
                      </tr>
                    </thead>
                    <tbody>
                      {dfa2.states.map(state =>
                        Object.entries(state.transitions).map(([symbol, next], idx) => (
                          <tr key={`${state.id}-${idx}`} className="hover:bg-gray-800/50">
                            <td className="p-2 border border-gray-700 font-mono">{state.id}</td>
                            <td className="p-2 border border-gray-700 font-mono">{symbol}</td>
                            <td className="p-2 border border-gray-700 font-mono">{next.id}</td>
                          </tr>
                        ))
                      )}
                    </tbody>
                  </table>
                </div>
              </div>
            </>
          )}
        </div>
      </div>
      
      {/* Dual Simulation Panel */}
      <div className="p-6 bg-gradient-to-br from-gray-800/50 to-gray-900/50 backdrop-blur border border-gray-700 rounded-xl">
        <h2 className="text-2xl font-bold mb-4 text-green-400">Dual Simulation Panel</h2>
        
        <div className="flex gap-4 mb-4">
          <input
            type="text"
            value={testString}
            onChange={(e) => setTestString(e.target.value)}
            className="flex-1 px-4 py-3 bg-gray-900/50 border border-gray-600 rounded-lg text-white font-mono text-lg"
            placeholder="Enter test string"
          />
          <button
            onClick={handleSimulate}
            disabled={!dfa1 || !dfa2 || !testString || isSimulating}
            className="px-8 py-3 bg-gradient-to-r from-green-600 to-blue-600 hover:from-green-500 hover:to-blue-500 disabled:from-gray-600 disabled:to-gray-700 rounded-lg font-bold shadow-lg transition-all hover:scale-105"
          >
            Simulate Both
          </button>
        </div>
        
        <div className="mb-4">
          <label className="block text-sm text-gray-400 mb-2">Simulation Speed</label>
          <div className="flex items-center gap-4">
            <Turtle size={20} />
            <input
              type="range"
              min="100"
              max="2000"
              step="100"
              value={simulationSpeed}
              onChange={(e) => setSimulationSpeed(parseInt(e.target.value))}
              className="flex-1"
            />
            <Zap size={20} />
          </div>
        </div>
        
        {simulation && !simulation.processing && (
          <motion.div
            initial={{ opacity: 0, y: 20 }}
            animate={{ opacity: 1, y: 0 }}
            className="mt-6 p-6 rounded-xl bg-gray-800/50 border border-gray-700"
          >
            <div className="grid grid-cols-2 gap-6">
              <div className={`p-4 rounded-lg ${simulation.accepted1 ? 'bg-green-900/20' : 'bg-red-900/20'}`}>
                <div className="text-xl font-bold mb-2">
                  {simulation.accepted1 ? '✅ DFA 1 ACCEPTED' : '❌ DFA 1 REJECTED'}
                </div>
                <div className="text-sm text-gray-300">
                  Path: {simulation.path1.join(' → ')}
                </div>
              </div>
              <div className={`p-4 rounded-lg ${simulation.accepted2 ? 'bg-green-900/20' : 'bg-red-900/20'}`}>
                <div className="text-xl font-bold mb-2">
                  {simulation.accepted2 ? '✅ DFA 2 ACCEPTED' : '❌ DFA 2 REJECTED'}
                </div>
                <div className="text-sm text-gray-300">
                  Path: {simulation.path2.join(' → ')}
                </div>
              </div>
            </div>
            
            {simulation.accepted1 === simulation.accepted2 && (
              <div className="mt-4 p-4 bg-purple-900/20 rounded-lg border border-purple-500">
                <div className="flex items-center gap-2">
                  <Sparkles className="text-purple-400" />
                  <span className="font-bold">
                    Consistent results confirm {simulation.accepted1 ? 'acceptance' : 'rejection'} for this string!
                  </span>
                </div>
              </div>
            )}
          </motion.div>
        )}
      </div>
    </motion.div>
  );
}
