from openai import OpenAI
client = OpenAI()

audio_file = open("res/audio.m4a", "rb")
transcription = client.audio.transcriptions.create(
  model="whisper-1",
  file=audio_file, 
  response_format="text",
  prompt="ZUCCMAP, lean, lean4, type theory, Curry-Howard isomorphism, Girard's paradox, Russell's paradox, Prop, lambda, cumulative"
)
print(transcription)
