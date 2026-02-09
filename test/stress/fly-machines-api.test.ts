import { describe, expect, it, vi } from 'vitest';
import { FlyCommandTokenProvider, FlyMachinesApiClient } from '../../scripts/stress/flyMachinesApi';

describe('FlyCommandTokenProvider', () => {
  it('uses cached token until forced refresh', async () => {
    const execFile = vi.fn().mockResolvedValue({
      stdout: 'fresh-token\n',
      stderr: '',
    });
    const provider = new FlyCommandTokenProvider({
      initialToken: 'cached-token',
      refreshCommand: 'flyctl auth token',
      execFile,
    });

    await expect(provider.getToken()).resolves.toBe('cached-token');
    expect(execFile).not.toHaveBeenCalled();

    await expect(provider.getToken(true)).resolves.toBe('fresh-token');
    expect(execFile).toHaveBeenCalledTimes(1);
    expect(execFile).toHaveBeenCalledWith('flyctl', ['auth', 'token'], { encoding: 'utf8' });
  });

  it('fails when no token source is configured', async () => {
    const provider = new FlyCommandTokenProvider({});
    await expect(provider.getToken()).rejects.toThrow(/missing Fly API token/);
  });
});

describe('FlyMachinesApiClient', () => {
  it('refreshes token and retries once on unauthorized', async () => {
    const tokenProvider = {
      getToken: vi.fn().mockResolvedValueOnce('expired-token').mockResolvedValueOnce('fresh-token'),
    };
    const fetchMock = vi
      .fn()
      .mockResolvedValueOnce(new Response('{"error":"unauthorized"}', { status: 403 }))
      .mockResolvedValueOnce(new Response(JSON.stringify({ id: 'machine-1' }), { status: 200 }));

    const client = new FlyMachinesApiClient(
      'https://api.machines.dev/v1',
      tokenProvider,
      fetchMock as unknown as typeof fetch,
    );

    const machine = await client.createMachine('app-name', { config: { image: 'worker' } } as never);
    expect(machine.id).toBe('machine-1');

    expect(tokenProvider.getToken).toHaveBeenCalledTimes(2);
    expect(tokenProvider.getToken).toHaveBeenNthCalledWith(1, false);
    expect(tokenProvider.getToken).toHaveBeenNthCalledWith(2, true);
    expect(fetchMock).toHaveBeenCalledTimes(2);
  });
});
