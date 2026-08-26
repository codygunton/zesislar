import {checkProfileSnapshot} from '../lib/test-utils'

test('importFromSafari', async () => {
  await checkProfileSnapshot('./sample/profiles/Safari/13.1/simple.html-recording.json')
})

test('importFromSafari 26.4', async () => {
  await checkProfileSnapshot('./sample/profiles/Safari/26.4/simple.html-recording.json')
})
