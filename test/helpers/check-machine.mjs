// Synthetic machine ports. Tests must not consult the runner's machine.
export const GiB = 1024 ** 3;
export function checkMachine(values = {}) {
  const machine = { count:40, free:128 * GiB, load:0, platform:'linux', battery:false, taskset:'/fake/taskset', ...values };
  return { machine, ports: {
    cores:() => Array.from({length:machine.count}, (_, index) => index + (machine.offset ?? 0)),
    memory:() => machine.free, load:() => machine.load, platform:machine.platform,
    battery:() => machine.battery, taskset:() => machine.taskset,
  } };
}
export function isolatedCheckCapacity(root, values) {
  return {...checkMachine(values).ports,queueRoot:`${root}/machine-check-queue`};
}
